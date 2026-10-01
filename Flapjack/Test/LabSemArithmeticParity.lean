import Flapjack.Compiler.Backend.LabSem.Arithmetic

/-! Native kernel replays of labsem_arithmetic_probe.out. Includes all8 cases,
Loc errors and self-OR, shift/division retained failure writes, signed overflow
and aliased destination order. Source states are otherwise arbitrary. -/
namespace Flapjack.Test.LabSemArithmeticParity
open Flapjack.Compiler.Backend.LabSem
variable (s : Flapjack.Compiler.Backend.LabSem.State 8 Unit Unit)

-- lab_arith_binop_add
example : let t := arithUpd (.binop .add 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then .word 255 else if r = 3 then .word 2 else .word 99, failed := false }
    t.regs 0 = .word 1 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_binop_sub
example : let t := arithUpd (.binop .sub 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then .word 1 else if r = 3 then .word 2 else .word 99, failed := false }
    t.regs 0 = .word 255 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_binop_and
example : let t := arithUpd (.binop .and 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then .word 240 else if r = 3 then .word 15 else .word 99, failed := false }
    t.regs 0 = .word 0 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_binop_or
example : let t := arithUpd (.binop .or 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then .word 240 else if r = 3 then .word 15 else .word 99, failed := false }
    t.regs 0 = .word 255 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_binop_xor
example : let t := arithUpd (.binop .xor 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then .word 170 else if r = 3 then .word 15 else .word 99, failed := false }
    t.regs 0 = .word 165 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_loc_or_self
example : let t := arithUpd (.binop .or 0 2 (.reg 2)) { s with regs := fun r => if r = 2 then .loc 4 5 else .word 99, failed := false }
    t.regs 0 = .loc 4 5 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_loc_or_other_reg
example : let t := arithUpd (.binop .or 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then .loc 4 5 else if r = 3 then .loc 4 5 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_loc_or_imm
example : let t := arithUpd (.binop .or 0 2 (.imm 0)) { s with regs := fun r => if r = 2 then .loc 4 5 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_loc_add_self
example : let t := arithUpd (.binop .add 0 2 (.reg 2)) { s with regs := fun r => if r = 2 then .loc 4 5 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_binop_right_loc
example : let t := arithUpd (.binop .add 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then .word 7 else if r = 3 then .loc 4 5 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_lsl_valid
example : let t := arithUpd (.shift .lsl 0 2 (.imm 7)) { s with regs := fun r => if r = 2 then .word 1 else .word 99, failed := false }
    t.regs 0 = .word 128 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_lsl_invalid
example : let t := arithUpd (.shift .lsl 0 2 (.imm 8)) { s with regs := fun r => if r = 2 then .word 128 else .word 99, failed := false }
    t.regs 0 = .word 0 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_lsr_invalid
example : let t := arithUpd (.shift .lsr 0 2 (.imm 8)) { s with regs := fun r => if r = 2 then .word 255 else .word 99, failed := false }
    t.regs 0 = .word 0 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_asr_invalid
example : let t := arithUpd (.shift .asr 0 2 (.imm 8)) { s with regs := fun r => if r = 2 then .word 128 else .word 99, failed := false }
    t.regs 0 = .word 255 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_ror_invalid
example : let t := arithUpd (.shift .ror 0 2 (.imm 8)) { s with regs := fun r => if r = 2 then .word 1 else .word 99, failed := false }
    t.regs 0 = .word 1 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_shift_source_loc
example : let t := arithUpd (.shift .lsl 0 2 (.imm 1)) { s with regs := fun r => if r = 2 then .loc 4 5 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_shift_amount_loc
example : let t := arithUpd (.shift .lsl 0 2 (.reg 3)) { s with regs := fun r => if r = 2 then .word 7 else if r = 3 then .loc 4 5 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_div_valid
example : let t := arithUpd (.div 0 2 3) { s with regs := fun r => if r = 2 then .word 17 else if r = 3 then .word 4 else .word 99, failed := false }
    t.regs 0 = .word 4 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_div_zero
example : let t := arithUpd (.div 0 2 3) { s with regs := fun r => if r = 2 then .word 17 else if r = 3 then .word 0 else .word 99, failed := false }
    t.regs 0 = .word 0 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_div_divisor_loc
example : let t := arithUpd (.div 0 2 3) { s with regs := fun r => if r = 2 then .word 17 else if r = 3 then .loc 4 5 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_div_dividend_loc
example : let t := arithUpd (.div 0 2 3) { s with regs := fun r => if r = 2 then .loc 4 5 else if r = 3 then .word 4 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true := ⟨rfl, rfl⟩

-- lab_arith_carry_nonzero
example : let t := arithUpd (.addCarry 0 2 3 1) { s with regs := fun r => if r = 2 then .word 255 else if r = 3 then .word 0 else if r = 1 then .word 5 else .word 99, failed := false }
    t.regs 0 = .word 0 ∧ t.failed = false ∧ t.regs 1 = .word 1 := ⟨rfl, rfl, rfl⟩

-- lab_arith_carry_zero
example : let t := arithUpd (.addCarry 0 2 3 1) { s with regs := fun r => if r = 2 then .word 255 else if r = 3 then .word 0 else if r = 1 then .word 0 else .word 99, failed := false }
    t.regs 0 = .word 255 ∧ t.failed = false ∧ t.regs 1 = .word 0 := ⟨rfl, rfl, rfl⟩

-- lab_arith_carry_flag_alias
example : let t := arithUpd (.addCarry 0 2 3 0) { s with regs := fun r => if r = 2 then .word 255 else if r = 3 then .word 0 else if r = 0 then .word 1 else .word 99, failed := false }
    t.regs 0 = .word 1 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_carry_loc
example : let t := arithUpd (.addCarry 0 2 3 1) { s with regs := fun r => if r = 2 then .word 255 else if r = 3 then .word 0 else if r = 1 then .loc 4 5 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true ∧ t.regs 1 = .loc 4 5 := ⟨rfl, rfl, rfl⟩

-- lab_arith_longmul_valid
example : let t := arithUpd (.longMul 0 1 2 3) { s with regs := fun r => if r = 2 then .word 255 else if r = 3 then .word 255 else .word 99, failed := false }
    t.regs 0 = .word 254 ∧ t.failed = false ∧ t.regs 1 = .word 1 := ⟨rfl, rfl, rfl⟩

-- lab_arith_longmul_dest_alias
example : let t := arithUpd (.longMul 0 0 2 3) { s with regs := fun r => if r = 2 then .word 255 else if r = 3 then .word 255 else .word 99, failed := false }
    t.regs 0 = .word 1 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_longmul_loc
example : let t := arithUpd (.longMul 0 1 2 3) { s with regs := fun r => if r = 2 then .word 255 else if r = 3 then .loc 4 5 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true ∧ t.regs 1 = .word 99 := ⟨rfl, rfl, rfl⟩

-- lab_arith_longdiv_valid
example : let t := arithUpd (.longDiv 0 1 2 3 4) { s with regs := fun r => if r = 2 then .word 1 else if r = 3 then .word 7 else if r = 4 then .word 3 else .word 99, failed := false }
    t.regs 0 = .word 87 ∧ t.failed = false ∧ t.regs 1 = .word 2 := ⟨rfl, rfl, rfl⟩

-- lab_arith_longdiv_dest_alias
example : let t := arithUpd (.longDiv 0 0 2 3 4) { s with regs := fun r => if r = 2 then .word 1 else if r = 3 then .word 7 else if r = 4 then .word 3 else .word 99, failed := false }
    t.regs 0 = .word 87 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_longdiv_quotient_bound
example : let t := arithUpd (.longDiv 0 1 2 3 4) { s with regs := fun r => if r = 2 then .word 1 else if r = 3 then .word 0 else if r = 4 then .word 1 else .word 99, failed := false }
    t.regs 0 = .word 0 ∧ t.failed = true ∧ t.regs 1 = .word 0 := ⟨rfl, rfl, rfl⟩

-- lab_arith_longdiv_zero
example : let t := arithUpd (.longDiv 0 1 2 3 4) { s with regs := fun r => if r = 2 then .word 1 else if r = 3 then .word 7 else if r = 4 then .word 0 else .word 99, failed := false }
    t.regs 0 = .word 0 ∧ t.failed = true ∧ t.regs 1 = .word 7 := ⟨rfl, rfl, rfl⟩

-- lab_arith_longdiv_loc
example : let t := arithUpd (.longDiv 0 1 2 3 4) { s with regs := fun r => if r = 2 then .loc 4 5 else if r = 3 then .word 7 else if r = 4 then .word 3 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true ∧ t.regs 1 = .word 99 := ⟨rfl, rfl, rfl⟩

-- lab_arith_add_overflow
example : let t := arithUpd (.addOverflow 0 2 3 1) { s with regs := fun r => if r = 2 then .word 127 else if r = 3 then .word 1 else .word 99, failed := false }
    t.regs 0 = .word 128 ∧ t.failed = false ∧ t.regs 1 = .word 1 := ⟨rfl, rfl, rfl⟩

-- lab_arith_add_no_overflow
example : let t := arithUpd (.addOverflow 0 2 3 1) { s with regs := fun r => if r = 2 then .word 1 else if r = 3 then .word 2 else .word 99, failed := false }
    t.regs 0 = .word 3 ∧ t.failed = false ∧ t.regs 1 = .word 0 := ⟨rfl, rfl, rfl⟩

-- lab_arith_add_negative_overflow
example : let t := arithUpd (.addOverflow 0 2 3 1) { s with regs := fun r => if r = 2 then .word 128 else if r = 3 then .word 255 else .word 99, failed := false }
    t.regs 0 = .word 127 ∧ t.failed = false ∧ t.regs 1 = .word 1 := ⟨rfl, rfl, rfl⟩

-- lab_arith_sub_overflow
example : let t := arithUpd (.subOverflow 0 2 3 1) { s with regs := fun r => if r = 2 then .word 128 else if r = 3 then .word 1 else .word 99, failed := false }
    t.regs 0 = .word 127 ∧ t.failed = false ∧ t.regs 1 = .word 1 := ⟨rfl, rfl, rfl⟩

-- lab_arith_sub_negative_rhs_overflow
example : let t := arithUpd (.subOverflow 0 2 3 1) { s with regs := fun r => if r = 2 then .word 127 else if r = 3 then .word 255 else .word 99, failed := false }
    t.regs 0 = .word 128 ∧ t.failed = false ∧ t.regs 1 = .word 1 := ⟨rfl, rfl, rfl⟩

-- lab_arith_sub_no_overflow
example : let t := arithUpd (.subOverflow 0 2 3 1) { s with regs := fun r => if r = 2 then .word 2 else if r = 3 then .word 1 else .word 99, failed := false }
    t.regs 0 = .word 1 ∧ t.failed = false ∧ t.regs 1 = .word 0 := ⟨rfl, rfl, rfl⟩

-- lab_arith_addOverflow_flag_alias
example : let t := arithUpd (.addOverflow 0 2 3 0) { s with regs := fun r => if r = 2 then .word 127 else if r = 3 then .word 1 else .word 99, failed := false }
    t.regs 0 = .word 1 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_addOverflow_loc
example : let t := arithUpd (.addOverflow 0 2 3 1) { s with regs := fun r => if r = 2 then .loc 4 5 else if r = 3 then .word 1 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true ∧ t.regs 1 = .word 99 := ⟨rfl, rfl, rfl⟩

-- lab_arith_subOverflow_flag_alias
example : let t := arithUpd (.subOverflow 0 2 3 0) { s with regs := fun r => if r = 2 then .word 128 else if r = 3 then .word 1 else .word 99, failed := false }
    t.regs 0 = .word 1 ∧ t.failed = false := ⟨rfl, rfl⟩

-- lab_arith_subOverflow_loc
example : let t := arithUpd (.subOverflow 0 2 3 1) { s with regs := fun r => if r = 2 then .loc 4 5 else if r = 3 then .word 1 else .word 99, failed := false }
    t.regs 0 = .word 99 ∧ t.failed = true ∧ t.regs 1 = .word 99 := ⟨rfl, rfl, rfl⟩

-- lab_arith_sticky_failed
example : let t := arithUpd (.binop .add 0 2 (.imm 1)) { s with regs := fun r => if r = 2 then .word 2 else .word 99, failed := true }
    t.regs 0 = .word 3 ∧ t.failed = true := ⟨rfl, rfl⟩

end Flapjack.Test.LabSemArithmeticParity
