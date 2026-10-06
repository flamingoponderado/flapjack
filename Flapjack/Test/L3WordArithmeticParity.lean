import Flapjack.RiscV.L3.Defs.WordArithmetic
set_option maxRecDepth 20000
namespace Flapjack.Test.L3WordArithmeticParity
open Flapjack.RiscV.L3
private def fixture (s : riscv_state) (mode : BitVec 2) (a b : BitVec 64) : riscv_state :=
 {s with procID := 7, c_MCSR := fun id => {s.c_MCSR id with mcpuid := {(s.c_MCSR id).mcpuid with ArchBase := mode}}, c_gpr := fun id r => if r = 1 then a else if r = 2 then b else s.c_gpr id r}

-- word_arithmetic_ADDIW_0_0_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,0) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- word_arithmetic_ADDIW_0_0_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,0) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- word_arithmetic_ADDIW_0_0_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,0) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- word_arithmetic_ADDIW_0_0_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,0) (fixture s 0 0 0) = signalException ExceptionType.Illegal_Instr (fixture s 0 0 0) := by rfl

-- word_arithmetic_ADDIW_0_1_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 0 18446744073709551615 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 1) := by rfl

-- word_arithmetic_ADDIW_0_1_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 0 18446744073709551615 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 1) := by rfl

-- word_arithmetic_ADDIW_0_1_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 0 18446744073709551615 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 1) := by rfl

-- word_arithmetic_ADDIW_0_1_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 0 18446744073709551615 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 1) := by rfl

-- word_arithmetic_ADDIW_0_2_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 0 2147483647 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483647 1) := by rfl

-- word_arithmetic_ADDIW_0_2_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 0 2147483647 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483647 1) := by rfl

-- word_arithmetic_ADDIW_0_2_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 0 2147483647 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483647 1) := by rfl

-- word_arithmetic_ADDIW_0_2_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 0 2147483647 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483647 1) := by rfl

-- word_arithmetic_ADDIW_0_3_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 0 2147483648 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 1) := by rfl

-- word_arithmetic_ADDIW_0_3_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 0 2147483648 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 1) := by rfl

-- word_arithmetic_ADDIW_0_3_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 0 2147483648 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 1) := by rfl

-- word_arithmetic_ADDIW_0_3_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 0 2147483648 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 1) := by rfl

-- word_arithmetic_ADDIW_0_4_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 0 4294967295 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967295 1) := by rfl

-- word_arithmetic_ADDIW_0_4_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 0 4294967295 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967295 1) := by rfl

-- word_arithmetic_ADDIW_0_4_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 0 4294967295 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967295 1) := by rfl

-- word_arithmetic_ADDIW_0_4_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 0 4294967295 1) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967295 1) := by rfl

-- word_arithmetic_ADDIW_0_5_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,4095) (fixture s 0 4294967297 4095) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 4095) := by rfl

-- word_arithmetic_ADDIW_0_5_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,4095) (fixture s 0 4294967297 4095) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 4095) := by rfl

-- word_arithmetic_ADDIW_0_5_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,4095) (fixture s 0 4294967297 4095) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 4095) := by rfl

-- word_arithmetic_ADDIW_0_5_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,4095) (fixture s 0 4294967297 4095) = signalException ExceptionType.Illegal_Instr (fixture s 0 4294967297 4095) := by rfl

-- word_arithmetic_ADDIW_0_6_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,2048) (fixture s 0 9223372036854775808 2048) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2048) := by rfl

-- word_arithmetic_ADDIW_0_6_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,2048) (fixture s 0 9223372036854775808 2048) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2048) := by rfl

-- word_arithmetic_ADDIW_0_6_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,2048) (fixture s 0 9223372036854775808 2048) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2048) := by rfl

-- word_arithmetic_ADDIW_0_6_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,2048) (fixture s 0 9223372036854775808 2048) = signalException ExceptionType.Illegal_Instr (fixture s 0 9223372036854775808 2048) := by rfl

-- word_arithmetic_ADDIW_0_7_0
example (s : riscv_state) : «dfn'ADDIW» (0,0,2047) (fixture s 0 17 2047) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 2047) := by rfl

-- word_arithmetic_ADDIW_0_7_1
example (s : riscv_state) : «dfn'ADDIW» (1,0,2047) (fixture s 0 17 2047) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 2047) := by rfl

-- word_arithmetic_ADDIW_0_7_2
example (s : riscv_state) : «dfn'ADDIW» (2,0,2047) (fixture s 0 17 2047) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 2047) := by rfl

-- word_arithmetic_ADDIW_0_7_7
example (s : riscv_state) : «dfn'ADDIW» (7,0,2047) (fixture s 0 17 2047) = signalException ExceptionType.Illegal_Instr (fixture s 0 17 2047) := by rfl

-- word_arithmetic_ADDIW_0_8_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,2048) (fixture s 0 18446744073709551615 2048) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2048) := by rfl

-- word_arithmetic_ADDIW_0_8_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,2048) (fixture s 0 18446744073709551615 2048) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2048) := by rfl

-- word_arithmetic_ADDIW_0_8_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,2048) (fixture s 0 18446744073709551615 2048) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2048) := by rfl

-- word_arithmetic_ADDIW_0_8_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,2048) (fixture s 0 18446744073709551615 2048) = signalException ExceptionType.Illegal_Instr (fixture s 0 18446744073709551615 2048) := by rfl

-- word_arithmetic_ADDIW_0_9_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,4095) (fixture s 0 2147483648 4095) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4095) := by rfl

-- word_arithmetic_ADDIW_0_9_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,4095) (fixture s 0 2147483648 4095) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4095) := by rfl

-- word_arithmetic_ADDIW_0_9_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,4095) (fixture s 0 2147483648 4095) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4095) := by rfl

-- word_arithmetic_ADDIW_0_9_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,4095) (fixture s 0 2147483648 4095) = signalException ExceptionType.Illegal_Instr (fixture s 0 2147483648 4095) := by rfl

-- word_arithmetic_ADDIW_2_0_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,0) (fixture s 2 0 0) = (let t := fixture s 2 0 0; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12))), 0) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_0_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,0) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12))), 1) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_0_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,0) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12))), 2) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_0_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,0) (fixture s 2 0 0) = (let t := fixture s 2 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12))), 7) (fixture s 2 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_1_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 2 18446744073709551615 1) = (let t := fixture s 2 18446744073709551615 1; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 0) (fixture s 2 18446744073709551615 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_1_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 2 18446744073709551615 1) = (let t := fixture s 2 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 1) (fixture s 2 18446744073709551615 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_1_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 2 18446744073709551615 1) = (let t := fixture s 2 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 2) (fixture s 2 18446744073709551615 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_1_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 2 18446744073709551615 1) = (let t := fixture s 2 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 7) (fixture s 2 18446744073709551615 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_2_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 2 2147483647 1) = (let t := fixture s 2 2147483647 1; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 0) (fixture s 2 2147483647 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067968 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_2_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 2 2147483647 1) = (let t := fixture s 2 2147483647 1; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 1) (fixture s 2 2147483647 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067968 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_2_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 2 2147483647 1) = (let t := fixture s 2 2147483647 1; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 2) (fixture s 2 2147483647 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067968 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_2_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 2 2147483647 1) = (let t := fixture s 2 2147483647 1; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 7) (fixture s 2 2147483647 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067968 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_3_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 2 2147483648 1) = (let t := fixture s 2 2147483648 1; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 0) (fixture s 2 2147483648 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067969 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_3_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 2 2147483648 1) = (let t := fixture s 2 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067969 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 1) (fixture s 2 2147483648 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067969 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_3_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 2 2147483648 1) = (let t := fixture s 2 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067969 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 2) (fixture s 2 2147483648 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067969 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_3_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 2 2147483648 1) = (let t := fixture s 2 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067969 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 7) (fixture s 2 2147483648 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067969 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_4_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 2 4294967295 1) = (let t := fixture s 2 4294967295 1; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 0) (fixture s 2 4294967295 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_4_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 2 4294967295 1) = (let t := fixture s 2 4294967295 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 1) (fixture s 2 4294967295 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_4_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 2 4294967295 1) = (let t := fixture s 2 4294967295 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 2) (fixture s 2 4294967295 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_4_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 2 4294967295 1) = (let t := fixture s 2 4294967295 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 7) (fixture s 2 4294967295 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_5_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,4095) (fixture s 2 4294967297 4095) = (let t := fixture s 2 4294967297 4095; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 0) (fixture s 2 4294967297 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_5_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,4095) (fixture s 2 4294967297 4095) = (let t := fixture s 2 4294967297 4095; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 1) (fixture s 2 4294967297 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_5_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,4095) (fixture s 2 4294967297 4095) = (let t := fixture s 2 4294967297 4095; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 2) (fixture s 2 4294967297 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_5_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,4095) (fixture s 2 4294967297 4095) = (let t := fixture s 2 4294967297 4095; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 7) (fixture s 2 4294967297 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_6_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,2048) (fixture s 2 9223372036854775808 2048) = (let t := fixture s 2 9223372036854775808 2048; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 0) (fixture s 2 9223372036854775808 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549568 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_6_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,2048) (fixture s 2 9223372036854775808 2048) = (let t := fixture s 2 9223372036854775808 2048; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 1) (fixture s 2 9223372036854775808 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549568 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_6_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,2048) (fixture s 2 9223372036854775808 2048) = (let t := fixture s 2 9223372036854775808 2048; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 2) (fixture s 2 9223372036854775808 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549568 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_6_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,2048) (fixture s 2 9223372036854775808 2048) = (let t := fixture s 2 9223372036854775808 2048; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 7) (fixture s 2 9223372036854775808 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549568 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_7_0
example (s : riscv_state) : «dfn'ADDIW» (0,0,2047) (fixture s 2 17 2047) = (let t := fixture s 2 17 2047; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12))), 0) (fixture s 2 17 2047) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12)))) = (2047 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_7_1
example (s : riscv_state) : «dfn'ADDIW» (1,0,2047) (fixture s 2 17 2047) = (let t := fixture s 2 17 2047; {t with c_gpr := holUpdate 7 (holUpdate 1 2047 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12))), 1) (fixture s 2 17 2047) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12)))) = (2047 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_7_2
example (s : riscv_state) : «dfn'ADDIW» (2,0,2047) (fixture s 2 17 2047) = (let t := fixture s 2 17 2047; {t with c_gpr := holUpdate 7 (holUpdate 2 2047 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12))), 2) (fixture s 2 17 2047) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12)))) = (2047 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_7_7
example (s : riscv_state) : «dfn'ADDIW» (7,0,2047) (fixture s 2 17 2047) = (let t := fixture s 2 17 2047; {t with c_gpr := holUpdate 7 (holUpdate 7 2047 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12))), 7) (fixture s 2 17 2047) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12)))) = (2047 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_8_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,2048) (fixture s 2 18446744073709551615 2048) = (let t := fixture s 2 18446744073709551615 2048; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 0) (fixture s 2 18446744073709551615 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549567 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_8_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,2048) (fixture s 2 18446744073709551615 2048) = (let t := fixture s 2 18446744073709551615 2048; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709549567 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 1) (fixture s 2 18446744073709551615 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549567 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_8_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,2048) (fixture s 2 18446744073709551615 2048) = (let t := fixture s 2 18446744073709551615 2048; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709549567 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 2) (fixture s 2 18446744073709551615 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549567 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_8_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,2048) (fixture s 2 18446744073709551615 2048) = (let t := fixture s 2 18446744073709551615 2048; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709549567 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 7) (fixture s 2 18446744073709551615 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549567 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_9_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,4095) (fixture s 2 2147483648 4095) = (let t := fixture s 2 2147483648 4095; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 0) (fixture s 2 2147483648 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_9_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,4095) (fixture s 2 2147483648 4095) = (let t := fixture s 2 2147483648 4095; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 1) (fixture s 2 2147483648 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_9_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,4095) (fixture s 2 2147483648 4095) = (let t := fixture s 2 2147483648 4095; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 2) (fixture s 2 2147483648 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_2_9_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,4095) (fixture s 2 2147483648 4095) = (let t := fixture s 2 2147483648 4095; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 7) (fixture s 2 2147483648 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_0_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,0) (fixture s 3 0 0) = (let t := fixture s 3 0 0; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12))), 0) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_0_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,0) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12))), 1) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_0_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,0) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12))), 2) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_0_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,0) (fixture s 3 0 0) = (let t := fixture s 3 0 0; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12))), 7) (fixture s 3 0 0) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (0 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_1_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 3 18446744073709551615 1) = (let t := fixture s 3 18446744073709551615 1; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 0) (fixture s 3 18446744073709551615 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_1_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 3 18446744073709551615 1) = (let t := fixture s 3 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 1) (fixture s 3 18446744073709551615 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_1_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 3 18446744073709551615 1) = (let t := fixture s 3 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 2) (fixture s 3 18446744073709551615 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_1_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 3 18446744073709551615 1) = (let t := fixture s 3 18446744073709551615 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 7) (fixture s 3 18446744073709551615 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_2_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 3 2147483647 1) = (let t := fixture s 3 2147483647 1; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 0) (fixture s 3 2147483647 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067968 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_2_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 3 2147483647 1) = (let t := fixture s 3 2147483647 1; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 1) (fixture s 3 2147483647 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067968 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_2_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 3 2147483647 1) = (let t := fixture s 3 2147483647 1; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 2) (fixture s 3 2147483647 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067968 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_2_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 3 2147483647 1) = (let t := fixture s 3 2147483647 1; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067968 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 7) (fixture s 3 2147483647 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483647 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067968 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_3_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 3 2147483648 1) = (let t := fixture s 3 2147483648 1; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 0) (fixture s 3 2147483648 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067969 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_3_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 3 2147483648 1) = (let t := fixture s 3 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744071562067969 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 1) (fixture s 3 2147483648 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067969 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_3_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 3 2147483648 1) = (let t := fixture s 3 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744071562067969 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 2) (fixture s 3 2147483648 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067969 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_3_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 3 2147483648 1) = (let t := fixture s 3 2147483648 1; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744071562067969 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 7) (fixture s 3 2147483648 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (18446744071562067969 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_4_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,1) (fixture s 3 4294967295 1) = (let t := fixture s 3 4294967295 1; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 0) (fixture s 3 4294967295 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_4_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,1) (fixture s 3 4294967295 1) = (let t := fixture s 3 4294967295 1; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 1) (fixture s 3 4294967295 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_4_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,1) (fixture s 3 4294967295 1) = (let t := fixture s 3 4294967295 1; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 2) (fixture s 3 4294967295 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_4_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,1) (fixture s 3 4294967295 1) = (let t := fixture s 3 4294967295 1; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12))), 7) (fixture s 3 4294967295 1) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967295 : BitVec 64) + BitVec.signExtend 64 (1 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_5_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,4095) (fixture s 3 4294967297 4095) = (let t := fixture s 3 4294967297 4095; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 0) (fixture s 3 4294967297 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_5_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,4095) (fixture s 3 4294967297 4095) = (let t := fixture s 3 4294967297 4095; {t with c_gpr := holUpdate 7 (holUpdate 1 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 1) (fixture s 3 4294967297 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_5_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,4095) (fixture s 3 4294967297 4095) = (let t := fixture s 3 4294967297 4095; {t with c_gpr := holUpdate 7 (holUpdate 2 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 2) (fixture s 3 4294967297 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_5_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,4095) (fixture s 3 4294967297 4095) = (let t := fixture s 3 4294967297 4095; {t with c_gpr := holUpdate 7 (holUpdate 7 0 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 7) (fixture s 3 4294967297 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((4294967297 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (0 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_6_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,2048) (fixture s 3 9223372036854775808 2048) = (let t := fixture s 3 9223372036854775808 2048; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 0) (fixture s 3 9223372036854775808 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549568 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_6_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,2048) (fixture s 3 9223372036854775808 2048) = (let t := fixture s 3 9223372036854775808 2048; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 1) (fixture s 3 9223372036854775808 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549568 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_6_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,2048) (fixture s 3 9223372036854775808 2048) = (let t := fixture s 3 9223372036854775808 2048; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 2) (fixture s 3 9223372036854775808 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549568 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_6_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,2048) (fixture s 3 9223372036854775808 2048) = (let t := fixture s 3 9223372036854775808 2048; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709549568 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 7) (fixture s 3 9223372036854775808 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((9223372036854775808 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549568 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_7_0
example (s : riscv_state) : «dfn'ADDIW» (0,0,2047) (fixture s 3 17 2047) = (let t := fixture s 3 17 2047; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12))), 0) (fixture s 3 17 2047) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12)))) = (2047 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_7_1
example (s : riscv_state) : «dfn'ADDIW» (1,0,2047) (fixture s 3 17 2047) = (let t := fixture s 3 17 2047; {t with c_gpr := holUpdate 7 (holUpdate 1 2047 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12))), 1) (fixture s 3 17 2047) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12)))) = (2047 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_7_2
example (s : riscv_state) : «dfn'ADDIW» (2,0,2047) (fixture s 3 17 2047) = (let t := fixture s 3 17 2047; {t with c_gpr := holUpdate 7 (holUpdate 2 2047 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12))), 2) (fixture s 3 17 2047) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12)))) = (2047 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_7_7
example (s : riscv_state) : «dfn'ADDIW» (7,0,2047) (fixture s 3 17 2047) = (let t := fixture s 3 17 2047; {t with c_gpr := holUpdate 7 (holUpdate 7 2047 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12))), 7) (fixture s 3 17 2047) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((0 : BitVec 64) + BitVec.signExtend 64 (2047 : BitVec 12)))) = (2047 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_8_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,2048) (fixture s 3 18446744073709551615 2048) = (let t := fixture s 3 18446744073709551615 2048; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 0) (fixture s 3 18446744073709551615 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549567 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_8_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,2048) (fixture s 3 18446744073709551615 2048) = (let t := fixture s 3 18446744073709551615 2048; {t with c_gpr := holUpdate 7 (holUpdate 1 18446744073709549567 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 1) (fixture s 3 18446744073709551615 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549567 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_8_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,2048) (fixture s 3 18446744073709551615 2048) = (let t := fixture s 3 18446744073709551615 2048; {t with c_gpr := holUpdate 7 (holUpdate 2 18446744073709549567 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 2) (fixture s 3 18446744073709551615 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549567 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_8_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,2048) (fixture s 3 18446744073709551615 2048) = (let t := fixture s 3 18446744073709551615 2048; {t with c_gpr := holUpdate 7 (holUpdate 7 18446744073709549567 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12))), 7) (fixture s 3 18446744073709551615 2048) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((18446744073709551615 : BitVec 64) + BitVec.signExtend 64 (2048 : BitVec 12)))) = (18446744073709549567 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_9_0
example (s : riscv_state) : «dfn'ADDIW» (0,1,4095) (fixture s 3 2147483648 4095) = (let t := fixture s 3 2147483648 4095; t) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 0) (fixture s 3 2147483648 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_9_1
example (s : riscv_state) : «dfn'ADDIW» (1,1,4095) (fixture s 3 2147483648 4095) = (let t := fixture s 3 2147483648 4095; {t with c_gpr := holUpdate 7 (holUpdate 1 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 1) (fixture s 3 2147483648 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_9_2
example (s : riscv_state) : «dfn'ADDIW» (2,1,4095) (fixture s 3 2147483648 4095) = (let t := fixture s 3 2147483648 4095; {t with c_gpr := holUpdate 7 (holUpdate 2 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 2) (fixture s 3 2147483648 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_ADDIW_3_9_7
example (s : riscv_state) : «dfn'ADDIW» (7,1,4095) (fixture s 3 2147483648 4095) = (let t := fixture s 3 2147483648 4095; {t with c_gpr := holUpdate 7 (holUpdate 7 2147483647 (t.c_gpr 7)) t.c_gpr}) := by
 change «write'GPR» (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12))), 7) (fixture s 3 2147483648 4095) = _
 have numeric : (BitVec.signExtend 64 (holWordExtract 32 31 0 ((2147483648 : BitVec 64) + BitVec.signExtend 64 (4095 : BitVec 12)))) = (2147483647 : BitVec 64) := by decide
 rw [numeric]
 rfl

-- word_arithmetic_symbolic_ADDIW
example (s : riscv_state) : «dfn'ADDIW» (0,0,0) ({fixture s 1 17 9 with exception := exception.NoException}) = (match in32BitMode () ({fixture s 1 17 9 with exception := exception.NoException}) with | (v,u) => if v then signalException ExceptionType.Illegal_Instr u else u) := by rfl

end Flapjack.Test.L3WordArithmeticParity
