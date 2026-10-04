import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameInstructions

namespace Flapjack.Test.WordToStackAsmNameInstructionsParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs.AsmNameInstructions
/- Fresh original HOL observations of validity, all seven guards, and actual compiled naming. -/

-- ani_1_skip_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_skip_guard=T
private theorem guard_ani_1_skip (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.skip) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.skip) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.skip) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_skip_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_1_const_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_const_guard=T
private theorem guard_ani_1_const (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_const_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_1_binop_imm_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_binop_imm_guard=T
private theorem guard_ani_1_binop_imm (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_binop_imm_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_1_binop_reg_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_binop_reg_guard=T
private theorem guard_ani_1_binop_reg (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_binop_reg_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_1_binop_or_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_binop_or_guard=T
private theorem guard_ani_1_binop_or (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_binop_or_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_1_shift_zero_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_shift_zero_guard=T
private theorem guard_ani_1_shift_zero (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_shift_zero_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_1_shift_one_valid=F
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = false := by
  exact of_decide_eq_true rfl

-- ani_1_shift_one_guard=F
example (c : AsmConfigExact 1) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_1_shift_one_target=F
example (c : AsmConfigExact 1) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_1_shift_reg_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_shift_reg_guard=T
private theorem guard_ani_1_shift_reg (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_shift_reg_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_1_div_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_div_guard=T
private theorem guard_ani_1_div (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_div_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_1_long_mul_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_long_mul_guard=T
private theorem guard_ani_1_long_mul (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_long_mul_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_1_long_div_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_long_div_guard=T
private theorem guard_ani_1_long_div (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_long_div_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_1_addCarry_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_addCarry_guard=T
private theorem guard_ani_1_addCarry (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_addCarry_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_1_addOverflow_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_addOverflow_guard=T
private theorem guard_ani_1_addOverflow (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_addOverflow_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_1_subOverflow_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_subOverflow_guard=T
private theorem guard_ani_1_subOverflow (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_subOverflow_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_1_load_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_load_guard=T
private theorem guard_ani_1_load (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_load_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_1_store_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_store_guard=T
private theorem guard_ani_1_store (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_store_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_1_load8_valid=F
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = false := by
  exact of_decide_eq_true rfl

-- ani_1_load8_guard=F
example (c : AsmConfigExact 1) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_1_load8_target=F
example (c : AsmConfigExact 1) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_1_store8_valid=F
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = false := by
  exact of_decide_eq_true rfl

-- ani_1_store8_guard=F
example (c : AsmConfigExact 1) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_1_store8_target=F
example (c : AsmConfigExact 1) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_1_load16_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_load16_guard=T
private theorem guard_ani_1_load16 (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_load16_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_1_store16_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_store16_guard=T
private theorem guard_ani_1_store16 (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_store16_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_1_load32_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_load32_guard=T
private theorem guard_ani_1_load32 (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_load32_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_1_store32_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_store32_guard=T
private theorem guard_ani_1_store32 (c : AsmConfigExact 1) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_1_store32_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_1_fpLess_valid=T


-- ani_1_fpLess_guard=T


-- ani_1_fpLess_target=T


-- ani_1_fpLessEqual_valid=T


-- ani_1_fpLessEqual_guard=T


-- ani_1_fpLessEqual_target=T


-- ani_1_fpEqual_valid=T


-- ani_1_fpEqual_guard=T


-- ani_1_fpEqual_target=T


-- ani_1_fpAbs_valid=T


-- ani_1_fpAbs_guard=T


-- ani_1_fpAbs_target=T


-- ani_1_fpNeg_valid=T


-- ani_1_fpNeg_guard=T


-- ani_1_fpNeg_target=T


-- ani_1_fpSqrt_valid=T


-- ani_1_fpSqrt_guard=T


-- ani_1_fpSqrt_target=T


-- ani_1_fpAdd_valid=T


-- ani_1_fpAdd_guard=T


-- ani_1_fpAdd_target=T


-- ani_1_fpSub_valid=T


-- ani_1_fpSub_guard=T


-- ani_1_fpSub_target=T


-- ani_1_fpMul_valid=T


-- ani_1_fpMul_guard=T


-- ani_1_fpMul_target=T


-- ani_1_fpDiv_valid=T


-- ani_1_fpDiv_guard=T


-- ani_1_fpDiv_target=T


-- ani_1_fpFma_valid=T


-- ani_1_fpFma_guard=T


-- ani_1_fpFma_target=T


-- ani_1_fpMov_valid=T


-- ani_1_fpMov_guard=T


-- ani_1_fpMov_target=T


-- ani_1_fpMovToReg_valid=T


-- ani_1_fpMovToReg_guard=T


-- ani_1_fpMovToReg_target=T


-- ani_1_fpMovFromReg_valid=T


-- ani_1_fpMovFromReg_guard=T


-- ani_1_fpMovFromReg_target=T


-- ani_1_fpToInt_valid=T


-- ani_1_fpToInt_guard=T


-- ani_1_fpToInt_target=T


-- ani_1_fpFromInt_valid=T


-- ani_1_fpFromInt_guard=T


-- ani_1_fpFromInt_target=T


-- ani_1_odd_carry_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_odd_carry_guard=F
example (c : AsmConfigExact 1) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_1_odd_carry_target=F
example (c : AsmConfigExact 1) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_1_odd_overflow_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_odd_overflow_guard=F
example (c : AsmConfigExact 1) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_1_odd_overflow_target=F
example (c : AsmConfigExact 1) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_1_odd_pair_valid=T


-- ani_1_odd_pair_guard=F


-- ani_1_odd_pair_target=T


-- ani_1_wide_ignored_second_valid=T


-- ani_1_wide_ignored_second_guard=F


-- ani_1_wide_ignored_second_target=T


-- ani_1_two_reg_reject_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_two_reg_reject_guard=F
example (c : AsmConfigExact 1) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_1_two_reg_reject_target=F
example (c : AsmConfigExact 1) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_1_or_exception_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_or_exception_guard=F
example (c : AsmConfigExact 1) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_1_or_exception_target=T
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_1_isa_div_valid=F
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 1)) = false := by
  exact of_decide_eq_true rfl

-- ani_1_isa_div_guard=F
example (c : AsmConfigExact 1) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_1_isa_div_target=F
example (c : AsmConfigExact 1) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_1_imm_reject_valid=F
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 1)) = false := by
  exact of_decide_eq_true rfl

-- ani_1_imm_reject_guard=F
example (c : AsmConfigExact 1) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_1_imm_reject_target=F
example (c : AsmConfigExact 1) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_1_fp_range_valid=F


-- ani_1_fp_range_guard=F


-- ani_1_fp_range_target=F


-- ani_1_fp_alias_valid=F


-- ani_1_fp_alias_guard=F


-- ani_1_fp_alias_target=F


-- ani_1_underflow_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_underflow_guard=F
example (c : AsmConfigExact 1) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_1_underflow_target=F
example (c : AsmConfigExact 1) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv

-- ani_1_minimum_shift_valid=T
example (c : AsmConfigExact 1) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 1)) = true := by
  exact of_decide_eq_true rfl

-- ani_1_minimum_shift_guard=F
example (c : AsmConfigExact 1) : ¬ (false = false ∧ postAllocConventionsHOL 4 (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 1)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 1)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 1)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 1)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 4+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<4) := by
  exact of_decide_eq_true rfl

-- ani_1_minimum_shift_target=F
example (c : AsmConfigExact 1) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (4,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_2_skip_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_skip_guard=T
private theorem guard_ani_2_skip (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.skip) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.skip) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.skip) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_skip_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_2_const_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_const_guard=T
private theorem guard_ani_2_const (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_const_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_2_binop_imm_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_binop_imm_guard=T
private theorem guard_ani_2_binop_imm (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_binop_imm_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_2_binop_reg_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_binop_reg_guard=T
private theorem guard_ani_2_binop_reg (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_binop_reg_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_2_binop_or_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_binop_or_guard=T
private theorem guard_ani_2_binop_or (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_binop_or_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_2_shift_zero_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_shift_zero_guard=T
private theorem guard_ani_2_shift_zero (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_shift_zero_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_2_shift_one_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_shift_one_guard=T
private theorem guard_ani_2_shift_one (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_shift_one_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_2_shift_reg_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_shift_reg_guard=T
private theorem guard_ani_2_shift_reg (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_shift_reg_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_2_div_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_div_guard=T
private theorem guard_ani_2_div (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_div_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_2_long_mul_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_long_mul_guard=T
private theorem guard_ani_2_long_mul (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_long_mul_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_2_long_div_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_long_div_guard=T
private theorem guard_ani_2_long_div (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_long_div_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_2_addCarry_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_addCarry_guard=T
private theorem guard_ani_2_addCarry (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_addCarry_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_2_addOverflow_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_addOverflow_guard=T
private theorem guard_ani_2_addOverflow (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_addOverflow_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_2_subOverflow_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_subOverflow_guard=T
private theorem guard_ani_2_subOverflow (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_subOverflow_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_2_load_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_load_guard=T
private theorem guard_ani_2_load (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_load_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_2_store_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_store_guard=T
private theorem guard_ani_2_store (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_store_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_2_load8_valid=F
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = false := by
  exact of_decide_eq_true rfl

-- ani_2_load8_guard=F
example (c : AsmConfigExact 2) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_2_load8_target=F
example (c : AsmConfigExact 2) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_2_store8_valid=F
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = false := by
  exact of_decide_eq_true rfl

-- ani_2_store8_guard=F
example (c : AsmConfigExact 2) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_2_store8_target=F
example (c : AsmConfigExact 2) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_2_load16_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_load16_guard=T
private theorem guard_ani_2_load16 (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_load16_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_2_store16_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_store16_guard=T
private theorem guard_ani_2_store16 (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_store16_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_2_load32_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_load32_guard=T
private theorem guard_ani_2_load32 (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_load32_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_2_store32_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_store32_guard=T
private theorem guard_ani_2_store32 (c : AsmConfigExact 2) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_2_store32_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_2_fpLess_valid=T


-- ani_2_fpLess_guard=T


-- ani_2_fpLess_target=T


-- ani_2_fpLessEqual_valid=T


-- ani_2_fpLessEqual_guard=T


-- ani_2_fpLessEqual_target=T


-- ani_2_fpEqual_valid=T


-- ani_2_fpEqual_guard=T


-- ani_2_fpEqual_target=T


-- ani_2_fpAbs_valid=T


-- ani_2_fpAbs_guard=T


-- ani_2_fpAbs_target=T


-- ani_2_fpNeg_valid=T


-- ani_2_fpNeg_guard=T


-- ani_2_fpNeg_target=T


-- ani_2_fpSqrt_valid=T


-- ani_2_fpSqrt_guard=T


-- ani_2_fpSqrt_target=T


-- ani_2_fpAdd_valid=T


-- ani_2_fpAdd_guard=T


-- ani_2_fpAdd_target=T


-- ani_2_fpSub_valid=T


-- ani_2_fpSub_guard=T


-- ani_2_fpSub_target=T


-- ani_2_fpMul_valid=T


-- ani_2_fpMul_guard=T


-- ani_2_fpMul_target=T


-- ani_2_fpDiv_valid=T


-- ani_2_fpDiv_guard=T


-- ani_2_fpDiv_target=T


-- ani_2_fpFma_valid=T


-- ani_2_fpFma_guard=T


-- ani_2_fpFma_target=T


-- ani_2_fpMov_valid=T


-- ani_2_fpMov_guard=T


-- ani_2_fpMov_target=T


-- ani_2_fpMovToReg_valid=T


-- ani_2_fpMovToReg_guard=T


-- ani_2_fpMovToReg_target=T


-- ani_2_fpMovFromReg_valid=T


-- ani_2_fpMovFromReg_guard=T


-- ani_2_fpMovFromReg_target=T


-- ani_2_fpToInt_valid=T


-- ani_2_fpToInt_guard=T


-- ani_2_fpToInt_target=T


-- ani_2_fpFromInt_valid=T


-- ani_2_fpFromInt_guard=T


-- ani_2_fpFromInt_target=T


-- ani_2_odd_carry_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_odd_carry_guard=F
example (c : AsmConfigExact 2) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_2_odd_carry_target=F
example (c : AsmConfigExact 2) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_2_odd_overflow_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_odd_overflow_guard=F
example (c : AsmConfigExact 2) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_2_odd_overflow_target=F
example (c : AsmConfigExact 2) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_2_odd_pair_valid=T


-- ani_2_odd_pair_guard=F


-- ani_2_odd_pair_target=T


-- ani_2_wide_ignored_second_valid=T


-- ani_2_wide_ignored_second_guard=F


-- ani_2_wide_ignored_second_target=T


-- ani_2_two_reg_reject_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_two_reg_reject_guard=F
example (c : AsmConfigExact 2) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_2_two_reg_reject_target=F
example (c : AsmConfigExact 2) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_2_or_exception_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_or_exception_guard=F
example (c : AsmConfigExact 2) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_2_or_exception_target=T
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_2_isa_div_valid=F
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 2)) = false := by
  exact of_decide_eq_true rfl

-- ani_2_isa_div_guard=F
example (c : AsmConfigExact 2) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_2_isa_div_target=F
example (c : AsmConfigExact 2) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_2_imm_reject_valid=F
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 2)) = false := by
  exact of_decide_eq_true rfl

-- ani_2_imm_reject_guard=F
example (c : AsmConfigExact 2) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_2_imm_reject_target=F
example (c : AsmConfigExact 2) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_2_fp_range_valid=F


-- ani_2_fp_range_guard=F


-- ani_2_fp_range_target=F


-- ani_2_fp_alias_valid=F


-- ani_2_fp_alias_guard=F


-- ani_2_fp_alias_target=F


-- ani_2_underflow_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_underflow_guard=F
example (c : AsmConfigExact 2) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_2_underflow_target=F
example (c : AsmConfigExact 2) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv

-- ani_2_minimum_shift_valid=T
example (c : AsmConfigExact 2) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) = true := by
  exact of_decide_eq_true rfl

-- ani_2_minimum_shift_guard=F
example (c : AsmConfigExact 2) : ¬ (false = false ∧ postAllocConventionsHOL 4 (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 4+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<4) := by
  exact of_decide_eq_true rfl

-- ani_2_minimum_shift_target=F
example (c : AsmConfigExact 2) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (4,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_8_skip_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_skip_guard=T
private theorem guard_ani_8_skip (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.skip) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.skip) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.skip) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_skip_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_const_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_const_guard=T
private theorem guard_ani_8_const (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_const_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_binop_imm_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_binop_imm_guard=T
private theorem guard_ani_8_binop_imm (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_binop_imm_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_8_binop_reg_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_binop_reg_guard=T
private theorem guard_ani_8_binop_reg (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_binop_reg_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_8_binop_or_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_binop_or_guard=T
private theorem guard_ani_8_binop_or (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_binop_or_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_8_shift_zero_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_shift_zero_guard=T
private theorem guard_ani_8_shift_zero (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_shift_zero_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_8_shift_one_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_shift_one_guard=T
private theorem guard_ani_8_shift_one (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_shift_one_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_8_shift_reg_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_shift_reg_guard=T
private theorem guard_ani_8_shift_reg (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_shift_reg_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_8_div_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_div_guard=T
private theorem guard_ani_8_div (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_div_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_long_mul_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_long_mul_guard=T
private theorem guard_ani_8_long_mul (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_long_mul_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_8_long_div_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_long_div_guard=T
private theorem guard_ani_8_long_div (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_long_div_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_addCarry_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_addCarry_guard=T
private theorem guard_ani_8_addCarry (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_addCarry_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_8_addOverflow_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_addOverflow_guard=T
private theorem guard_ani_8_addOverflow (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_addOverflow_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_8_subOverflow_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_subOverflow_guard=T
private theorem guard_ani_8_subOverflow (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_subOverflow_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_8_load_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_load_guard=T
private theorem guard_ani_8_load (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_load_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_store_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_store_guard=T
private theorem guard_ani_8_store (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_store_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_load8_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_load8_guard=T
private theorem guard_ani_8_load8 (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_load8_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_store8_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_store8_guard=T
private theorem guard_ani_8_store8 (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_store8_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_load16_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_load16_guard=T
private theorem guard_ani_8_load16 (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_load16_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_store16_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_store16_guard=T
private theorem guard_ani_8_store16 (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_store16_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_load32_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_load32_guard=T
private theorem guard_ani_8_load32 (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_load32_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_store32_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_store32_guard=T
private theorem guard_ani_8_store32 (c : AsmConfigExact 8) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_8_store32_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_8_fpLess_valid=T


-- ani_8_fpLess_guard=T


-- ani_8_fpLess_target=T


-- ani_8_fpLessEqual_valid=T


-- ani_8_fpLessEqual_guard=T


-- ani_8_fpLessEqual_target=T


-- ani_8_fpEqual_valid=T


-- ani_8_fpEqual_guard=T


-- ani_8_fpEqual_target=T


-- ani_8_fpAbs_valid=T


-- ani_8_fpAbs_guard=T


-- ani_8_fpAbs_target=T


-- ani_8_fpNeg_valid=T


-- ani_8_fpNeg_guard=T


-- ani_8_fpNeg_target=T


-- ani_8_fpSqrt_valid=T


-- ani_8_fpSqrt_guard=T


-- ani_8_fpSqrt_target=T


-- ani_8_fpAdd_valid=T


-- ani_8_fpAdd_guard=T


-- ani_8_fpAdd_target=T


-- ani_8_fpSub_valid=T


-- ani_8_fpSub_guard=T


-- ani_8_fpSub_target=T


-- ani_8_fpMul_valid=T


-- ani_8_fpMul_guard=T


-- ani_8_fpMul_target=T


-- ani_8_fpDiv_valid=T


-- ani_8_fpDiv_guard=T


-- ani_8_fpDiv_target=T


-- ani_8_fpFma_valid=T


-- ani_8_fpFma_guard=T


-- ani_8_fpFma_target=T


-- ani_8_fpMov_valid=T


-- ani_8_fpMov_guard=T


-- ani_8_fpMov_target=T


-- ani_8_fpMovToReg_valid=T


-- ani_8_fpMovToReg_guard=T


-- ani_8_fpMovToReg_target=T


-- ani_8_fpMovFromReg_valid=T


-- ani_8_fpMovFromReg_guard=T


-- ani_8_fpMovFromReg_target=T


-- ani_8_fpToInt_valid=T


-- ani_8_fpToInt_guard=T


-- ani_8_fpToInt_target=T


-- ani_8_fpFromInt_valid=T


-- ani_8_fpFromInt_guard=T


-- ani_8_fpFromInt_target=T


-- ani_8_odd_carry_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_odd_carry_guard=F
example (c : AsmConfigExact 8) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_8_odd_carry_target=F
example (c : AsmConfigExact 8) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_8_odd_overflow_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_odd_overflow_guard=F
example (c : AsmConfigExact 8) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_8_odd_overflow_target=F
example (c : AsmConfigExact 8) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_8_odd_pair_valid=T


-- ani_8_odd_pair_guard=F


-- ani_8_odd_pair_target=T


-- ani_8_wide_ignored_second_valid=T


-- ani_8_wide_ignored_second_guard=F


-- ani_8_wide_ignored_second_target=T


-- ani_8_two_reg_reject_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_two_reg_reject_guard=F
example (c : AsmConfigExact 8) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_8_two_reg_reject_target=F
example (c : AsmConfigExact 8) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_8_or_exception_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_or_exception_guard=F
example (c : AsmConfigExact 8) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_8_or_exception_target=T
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_8_isa_div_valid=F
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 8)) = false := by
  exact of_decide_eq_true rfl

-- ani_8_isa_div_guard=F
example (c : AsmConfigExact 8) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_8_isa_div_target=F
example (c : AsmConfigExact 8) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_8_imm_reject_valid=F
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 8)) = false := by
  exact of_decide_eq_true rfl

-- ani_8_imm_reject_guard=F
example (c : AsmConfigExact 8) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_8_imm_reject_target=F
example (c : AsmConfigExact 8) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_8_fp_range_valid=F


-- ani_8_fp_range_guard=F


-- ani_8_fp_range_target=F


-- ani_8_fp_alias_valid=F


-- ani_8_fp_alias_guard=F


-- ani_8_fp_alias_target=F


-- ani_8_underflow_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_underflow_guard=F
example (c : AsmConfigExact 8) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_8_underflow_target=F
example (c : AsmConfigExact 8) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv

-- ani_8_minimum_shift_valid=T
example (c : AsmConfigExact 8) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 8)) = true := by
  exact of_decide_eq_true rfl

-- ani_8_minimum_shift_guard=F
example (c : AsmConfigExact 8) : ¬ (false = false ∧ postAllocConventionsHOL 4 (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 8)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 8)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 8)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 8)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 4+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<4) := by
  exact of_decide_eq_true rfl

-- ani_8_minimum_shift_target=F
example (c : AsmConfigExact 8) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (4,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_32_skip_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_skip_guard=T
private theorem guard_ani_32_skip (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.skip) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.skip) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.skip) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_skip_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_const_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_const_guard=T
private theorem guard_ani_32_const (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_const_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_binop_imm_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_binop_imm_guard=T
private theorem guard_ani_32_binop_imm (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_binop_imm_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_32_binop_reg_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_binop_reg_guard=T
private theorem guard_ani_32_binop_reg (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_binop_reg_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_32_binop_or_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_binop_or_guard=T
private theorem guard_ani_32_binop_or (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_binop_or_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_32_shift_zero_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_shift_zero_guard=T
private theorem guard_ani_32_shift_zero (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_shift_zero_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_32_shift_one_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_shift_one_guard=T
private theorem guard_ani_32_shift_one (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_shift_one_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_32_shift_reg_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_shift_reg_guard=T
private theorem guard_ani_32_shift_reg (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_shift_reg_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_32_div_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_div_guard=T
private theorem guard_ani_32_div (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_div_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_long_mul_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_long_mul_guard=T
private theorem guard_ani_32_long_mul (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_long_mul_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_32_long_div_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_long_div_guard=T
private theorem guard_ani_32_long_div (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_long_div_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_addCarry_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_addCarry_guard=T
private theorem guard_ani_32_addCarry (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_addCarry_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_32_addOverflow_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_addOverflow_guard=T
private theorem guard_ani_32_addOverflow (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_addOverflow_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_32_subOverflow_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_subOverflow_guard=T
private theorem guard_ani_32_subOverflow (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_subOverflow_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_32_load_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_load_guard=T
private theorem guard_ani_32_load (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_load_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_store_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_store_guard=T
private theorem guard_ani_32_store (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_store_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_load8_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_load8_guard=T
private theorem guard_ani_32_load8 (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_load8_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_store8_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_store8_guard=T
private theorem guard_ani_32_store8 (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_store8_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_load16_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_load16_guard=T
private theorem guard_ani_32_load16 (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_load16_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_store16_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_store16_guard=T
private theorem guard_ani_32_store16 (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_store16_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_load32_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_load32_guard=T
private theorem guard_ani_32_load32 (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_load32_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_store32_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_store32_guard=T
private theorem guard_ani_32_store32 (c : AsmConfigExact 32) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_32_store32_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_32_fpLess_valid=T


-- ani_32_fpLess_guard=T


-- ani_32_fpLess_target=T


-- ani_32_fpLessEqual_valid=T


-- ani_32_fpLessEqual_guard=T


-- ani_32_fpLessEqual_target=T


-- ani_32_fpEqual_valid=T


-- ani_32_fpEqual_guard=T


-- ani_32_fpEqual_target=T


-- ani_32_fpAbs_valid=T


-- ani_32_fpAbs_guard=T


-- ani_32_fpAbs_target=T


-- ani_32_fpNeg_valid=T


-- ani_32_fpNeg_guard=T


-- ani_32_fpNeg_target=T


-- ani_32_fpSqrt_valid=T


-- ani_32_fpSqrt_guard=T


-- ani_32_fpSqrt_target=T


-- ani_32_fpAdd_valid=T


-- ani_32_fpAdd_guard=T


-- ani_32_fpAdd_target=T


-- ani_32_fpSub_valid=T


-- ani_32_fpSub_guard=T


-- ani_32_fpSub_target=T


-- ani_32_fpMul_valid=T


-- ani_32_fpMul_guard=T


-- ani_32_fpMul_target=T


-- ani_32_fpDiv_valid=T


-- ani_32_fpDiv_guard=T


-- ani_32_fpDiv_target=T


-- ani_32_fpFma_valid=T


-- ani_32_fpFma_guard=T


-- ani_32_fpFma_target=T


-- ani_32_fpMov_valid=T


-- ani_32_fpMov_guard=T


-- ani_32_fpMov_target=T


-- ani_32_fpMovToReg_valid=T


-- ani_32_fpMovToReg_guard=T


-- ani_32_fpMovToReg_target=T


-- ani_32_fpMovFromReg_valid=T


-- ani_32_fpMovFromReg_guard=T


-- ani_32_fpMovFromReg_target=T


-- ani_32_fpToInt_valid=T


-- ani_32_fpToInt_guard=T


-- ani_32_fpToInt_target=T


-- ani_32_fpFromInt_valid=T


-- ani_32_fpFromInt_guard=T


-- ani_32_fpFromInt_target=T


-- ani_32_odd_carry_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_odd_carry_guard=F
example (c : AsmConfigExact 32) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_32_odd_carry_target=F
example (c : AsmConfigExact 32) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_32_odd_overflow_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_odd_overflow_guard=F
example (c : AsmConfigExact 32) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_32_odd_overflow_target=F
example (c : AsmConfigExact 32) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_32_odd_pair_valid=T


-- ani_32_odd_pair_guard=F


-- ani_32_odd_pair_target=F


-- ani_32_wide_ignored_second_valid=T


-- ani_32_wide_ignored_second_guard=F


-- ani_32_wide_ignored_second_target=T


-- ani_32_two_reg_reject_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_two_reg_reject_guard=F
example (c : AsmConfigExact 32) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_32_two_reg_reject_target=F
example (c : AsmConfigExact 32) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_32_or_exception_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_or_exception_guard=F
example (c : AsmConfigExact 32) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_32_or_exception_target=T
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_32_isa_div_valid=F
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 32)) = false := by
  exact of_decide_eq_true rfl

-- ani_32_isa_div_guard=F
example (c : AsmConfigExact 32) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_32_isa_div_target=F
example (c : AsmConfigExact 32) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_32_imm_reject_valid=F
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 32)) = false := by
  exact of_decide_eq_true rfl

-- ani_32_imm_reject_guard=F
example (c : AsmConfigExact 32) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_32_imm_reject_target=F
example (c : AsmConfigExact 32) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_32_fp_range_valid=F


-- ani_32_fp_range_guard=F


-- ani_32_fp_range_target=F


-- ani_32_fp_alias_valid=F


-- ani_32_fp_alias_guard=F


-- ani_32_fp_alias_target=F


-- ani_32_underflow_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_underflow_guard=F
example (c : AsmConfigExact 32) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_32_underflow_target=F
example (c : AsmConfigExact 32) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv

-- ani_32_minimum_shift_valid=T
example (c : AsmConfigExact 32) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) = true := by
  exact of_decide_eq_true rfl

-- ani_32_minimum_shift_guard=F
example (c : AsmConfigExact 32) : ¬ (false = false ∧ postAllocConventionsHOL 4 (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 4+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<4) := by
  exact of_decide_eq_true rfl

-- ani_32_minimum_shift_target=F
example (c : AsmConfigExact 32) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (4,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_64_skip_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_skip_guard=T
private theorem guard_ani_64_skip (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.skip) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.skip) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.skip) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_skip_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_const_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_const_guard=T
private theorem guard_ani_64_const (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_const_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_binop_imm_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_binop_imm_guard=T
private theorem guard_ani_64_binop_imm (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_binop_imm_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_64_binop_reg_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_binop_reg_guard=T
private theorem guard_ani_64_binop_reg (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_binop_reg_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_64_binop_or_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_binop_or_guard=T
private theorem guard_ani_64_binop_or (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_binop_or_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_64_shift_zero_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_shift_zero_guard=T
private theorem guard_ani_64_shift_zero (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_shift_zero_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_64_shift_one_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_shift_one_guard=T
private theorem guard_ani_64_shift_one (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_shift_one_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_64_shift_reg_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_shift_reg_guard=T
private theorem guard_ani_64_shift_reg (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_shift_reg_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_64_div_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_div_guard=T
private theorem guard_ani_64_div (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_div_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_long_mul_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_long_mul_guard=T
private theorem guard_ani_64_long_mul (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_long_mul_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_64_long_div_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_long_div_guard=T
private theorem guard_ani_64_long_div (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_long_div_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_addCarry_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_addCarry_guard=T
private theorem guard_ani_64_addCarry (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_addCarry_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_64_addOverflow_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_addOverflow_guard=T
private theorem guard_ani_64_addOverflow (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_addOverflow_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_64_subOverflow_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_subOverflow_guard=T
private theorem guard_ani_64_subOverflow (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_subOverflow_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_64_load_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_load_guard=T
private theorem guard_ani_64_load (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_load_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_store_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_store_guard=T
private theorem guard_ani_64_store (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_store_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_load8_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_load8_guard=T
private theorem guard_ani_64_load8 (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_load8_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_store8_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_store8_guard=T
private theorem guard_ani_64_store8 (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_store8_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_load16_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_load16_guard=T
private theorem guard_ani_64_load16 (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_load16_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_store16_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_store16_guard=T
private theorem guard_ani_64_store16 (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_store16_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_load32_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_load32_guard=T
private theorem guard_ani_64_load32 (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_load32_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_store32_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_store32_guard=T
private theorem guard_ani_64_store32 (c : AsmConfigExact 64) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_64_store32_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_64_fpLess_valid=T


-- ani_64_fpLess_guard=T


-- ani_64_fpLess_target=T


-- ani_64_fpLessEqual_valid=T


-- ani_64_fpLessEqual_guard=T


-- ani_64_fpLessEqual_target=T


-- ani_64_fpEqual_valid=T


-- ani_64_fpEqual_guard=T


-- ani_64_fpEqual_target=T


-- ani_64_fpAbs_valid=T


-- ani_64_fpAbs_guard=T


-- ani_64_fpAbs_target=T


-- ani_64_fpNeg_valid=T


-- ani_64_fpNeg_guard=T


-- ani_64_fpNeg_target=T


-- ani_64_fpSqrt_valid=T


-- ani_64_fpSqrt_guard=T


-- ani_64_fpSqrt_target=T


-- ani_64_fpAdd_valid=T


-- ani_64_fpAdd_guard=T


-- ani_64_fpAdd_target=T


-- ani_64_fpSub_valid=T


-- ani_64_fpSub_guard=T


-- ani_64_fpSub_target=T


-- ani_64_fpMul_valid=T


-- ani_64_fpMul_guard=T


-- ani_64_fpMul_target=T


-- ani_64_fpDiv_valid=T


-- ani_64_fpDiv_guard=T


-- ani_64_fpDiv_target=T


-- ani_64_fpFma_valid=T


-- ani_64_fpFma_guard=T


-- ani_64_fpFma_target=T


-- ani_64_fpMov_valid=T


-- ani_64_fpMov_guard=T


-- ani_64_fpMov_target=T


-- ani_64_fpMovToReg_valid=T


-- ani_64_fpMovToReg_guard=T


-- ani_64_fpMovToReg_target=T


-- ani_64_fpMovFromReg_valid=T


-- ani_64_fpMovFromReg_guard=T


-- ani_64_fpMovFromReg_target=T


-- ani_64_fpToInt_valid=T


-- ani_64_fpToInt_guard=T


-- ani_64_fpToInt_target=T


-- ani_64_fpFromInt_valid=T


-- ani_64_fpFromInt_guard=T


-- ani_64_fpFromInt_target=T


-- ani_64_odd_carry_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_odd_carry_guard=F
example (c : AsmConfigExact 64) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_64_odd_carry_target=F
example (c : AsmConfigExact 64) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_64_odd_overflow_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_odd_overflow_guard=F
example (c : AsmConfigExact 64) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_64_odd_overflow_target=F
example (c : AsmConfigExact 64) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_64_odd_pair_valid=T


-- ani_64_odd_pair_guard=F


-- ani_64_odd_pair_target=T


-- ani_64_wide_ignored_second_valid=T


-- ani_64_wide_ignored_second_guard=T


-- ani_64_wide_ignored_second_target=T


-- ani_64_two_reg_reject_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_two_reg_reject_guard=F
example (c : AsmConfigExact 64) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_64_two_reg_reject_target=F
example (c : AsmConfigExact 64) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_64_or_exception_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_or_exception_guard=F
example (c : AsmConfigExact 64) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_64_or_exception_target=T
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_64_isa_div_valid=F
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 64)) = false := by
  exact of_decide_eq_true rfl

-- ani_64_isa_div_guard=F
example (c : AsmConfigExact 64) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_64_isa_div_target=F
example (c : AsmConfigExact 64) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_64_imm_reject_valid=F
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 64)) = false := by
  exact of_decide_eq_true rfl

-- ani_64_imm_reject_guard=F
example (c : AsmConfigExact 64) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_64_imm_reject_target=F
example (c : AsmConfigExact 64) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_64_fp_range_valid=F


-- ani_64_fp_range_guard=F


-- ani_64_fp_range_target=F


-- ani_64_fp_alias_valid=F


-- ani_64_fp_alias_guard=F


-- ani_64_fp_alias_target=F


-- ani_64_underflow_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_underflow_guard=F
example (c : AsmConfigExact 64) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_64_underflow_target=F
example (c : AsmConfigExact 64) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv

-- ani_64_minimum_shift_valid=T
example (c : AsmConfigExact 64) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 64)) = true := by
  exact of_decide_eq_true rfl

-- ani_64_minimum_shift_guard=F
example (c : AsmConfigExact 64) : ¬ (false = false ∧ postAllocConventionsHOL 4 (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 64)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 64)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 64)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 64)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 4+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<4) := by
  exact of_decide_eq_true rfl

-- ani_64_minimum_shift_target=F
example (c : AsmConfigExact 64) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (4,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_80_skip_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_skip_guard=T
private theorem guard_ani_80_skip (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.skip) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.skip) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.skip) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.skip) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_skip_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_const_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_const_guard=T
private theorem guard_ani_80_const (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_const_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_binop_imm_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_binop_imm_guard=T
private theorem guard_ani_80_binop_imm (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_binop_imm_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_80_binop_reg_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_binop_reg_guard=T
private theorem guard_ani_80_binop_reg (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_binop_reg_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_80_binop_or_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_binop_or_guard=T
private theorem guard_ani_80_binop_or (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_binop_or_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_80_shift_zero_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_shift_zero_guard=T
private theorem guard_ani_80_shift_zero (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_shift_zero_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_80_shift_one_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_shift_one_guard=T
private theorem guard_ani_80_shift_one (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_shift_one_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_80_shift_reg_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_shift_reg_guard=T
private theorem guard_ani_80_shift_reg (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_shift_reg_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_80_div_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_div_guard=T
private theorem guard_ani_80_div (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_div_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_long_mul_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_long_mul_guard=T
private theorem guard_ani_80_long_mul (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_long_mul_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_80_long_div_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_long_div_guard=T
private theorem guard_ani_80_long_div (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_long_div_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_addCarry_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_addCarry_guard=T
private theorem guard_ani_80_addCarry (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_addCarry_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_80_addOverflow_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_addOverflow_guard=T
private theorem guard_ani_80_addOverflow (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_addOverflow_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_80_subOverflow_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_subOverflow_guard=T
private theorem guard_ani_80_subOverflow (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_subOverflow_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_80_load_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_load_guard=T
private theorem guard_ani_80_load (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_load_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_store_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_store_guard=T
private theorem guard_ani_80_store (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_store_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_load8_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_load8_guard=T
private theorem guard_ani_80_load8 (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_load8_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_store8_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_store8_guard=T
private theorem guard_ani_80_store8 (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_store8_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_load16_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_load16_guard=T
private theorem guard_ani_80_load16 (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_load16_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_store16_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_store16_guard=T
private theorem guard_ani_80_store16 (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_store16_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_load32_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_load32_guard=T
private theorem guard_ani_80_load32 (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_load32_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_store32_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_store32_guard=T
private theorem guard_ani_80_store32 (c : AsmConfigExact 80) : false = false ∧ postAllocConventionsHOL 5 (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5 := by
  exact of_decide_eq_true rfl

-- ani_80_store32_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv

-- ani_80_fpLess_valid=T


-- ani_80_fpLess_guard=T


-- ani_80_fpLess_target=T


-- ani_80_fpLessEqual_valid=T


-- ani_80_fpLessEqual_guard=T


-- ani_80_fpLessEqual_target=T


-- ani_80_fpEqual_valid=T


-- ani_80_fpEqual_guard=T


-- ani_80_fpEqual_target=T


-- ani_80_fpAbs_valid=T


-- ani_80_fpAbs_guard=T


-- ani_80_fpAbs_target=T


-- ani_80_fpNeg_valid=T


-- ani_80_fpNeg_guard=T


-- ani_80_fpNeg_target=T


-- ani_80_fpSqrt_valid=T


-- ani_80_fpSqrt_guard=T


-- ani_80_fpSqrt_target=T


-- ani_80_fpAdd_valid=T


-- ani_80_fpAdd_guard=T


-- ani_80_fpAdd_target=T


-- ani_80_fpSub_valid=T


-- ani_80_fpSub_guard=T


-- ani_80_fpSub_target=T


-- ani_80_fpMul_valid=T


-- ani_80_fpMul_guard=T


-- ani_80_fpMul_target=T


-- ani_80_fpDiv_valid=T


-- ani_80_fpDiv_guard=T


-- ani_80_fpDiv_target=T


-- ani_80_fpFma_valid=T


-- ani_80_fpFma_guard=T


-- ani_80_fpFma_target=T


-- ani_80_fpMov_valid=T


-- ani_80_fpMov_guard=T


-- ani_80_fpMov_target=T


-- ani_80_fpMovToReg_valid=T


-- ani_80_fpMovToReg_guard=T


-- ani_80_fpMovToReg_target=T


-- ani_80_fpMovFromReg_valid=T


-- ani_80_fpMovFromReg_guard=T


-- ani_80_fpMovFromReg_target=T


-- ani_80_fpToInt_valid=T


-- ani_80_fpToInt_guard=T


-- ani_80_fpToInt_target=T


-- ani_80_fpFromInt_valid=T


-- ani_80_fpFromInt_guard=T


-- ani_80_fpFromInt_target=T


-- ani_80_odd_carry_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_odd_carry_guard=F
example (c : AsmConfigExact 80) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_80_odd_carry_target=F
example (c : AsmConfigExact 80) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 3 3 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_80_odd_overflow_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_odd_overflow_guard=F
example (c : AsmConfigExact 80) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_80_odd_overflow_target=F
example (c : AsmConfigExact 80) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 3 3 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_80_odd_pair_valid=T


-- ani_80_odd_pair_guard=F


-- ani_80_odd_pair_target=T


-- ani_80_wide_ignored_second_valid=T


-- ani_80_wide_ignored_second_guard=F


-- ani_80_wide_ignored_second_target=T


-- ani_80_two_reg_reject_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_two_reg_reject_guard=F
example (c : AsmConfigExact 80) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_80_two_reg_reject_target=F
example (c : AsmConfigExact 80) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_80_or_exception_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_or_exception_guard=F
example (c : AsmConfigExact 80) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_80_or_exception_target=T
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  cbv; simp

-- ani_80_isa_div_valid=F
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 80)) = false := by
  exact of_decide_eq_true rfl

-- ani_80_isa_div_guard=F
example (c : AsmConfigExact 80) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_80_isa_div_target=F
example (c : AsmConfigExact 80) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 4 2 6)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_80_imm_reject_valid=F
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 80)) = false := by
  exact of_decide_eq_true rfl

-- ani_80_imm_reject_guard=F
example (c : AsmConfigExact 80) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_80_imm_reject_target=F
example (c : AsmConfigExact 80) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 2))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv; simp

-- ani_80_fp_range_valid=F


-- ani_80_fp_range_guard=F


-- ani_80_fp_range_target=F


-- ani_80_fp_alias_valid=F


-- ani_80_fp_alias_guard=F


-- ani_80_fp_alias_target=F


-- ani_80_underflow_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_underflow_guard=F
example (c : AsmConfigExact 80) : ¬ (false = false ∧ postAllocConventionsHOL 5 (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 5+1 < ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<5) := by
  exact of_decide_eq_true rfl

-- ani_80_underflow_target=F
example (c : AsmConfigExact 80) : ¬ (stackAsmName ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 0, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1) := by
  cbv

-- ani_80_minimum_shift_valid=T
example (c : AsmConfigExact 80) : fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) = true := by
  exact of_decide_eq_true rfl

-- ani_80_minimum_shift_guard=F
example (c : AsmConfigExact 80) : ¬ (false = false ∧ postAllocConventionsHOL 4 (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) = true ∧ fullInstOkLessExact ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) = true ∧ (({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).twoRegArith = true → everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i)) (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) = true) ∧ (noShareInstSubprogsHOL (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) = true ∨ ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).isa ≠ .ag32) ∧ 4+1 < ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).regCount - ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }).avoidRegs.length ∧ 4<4) := by
  exact of_decide_eq_true rfl

-- ani_80_minimum_shift_target=F
example (c : AsmConfigExact 80) : ¬ (stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 2 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (4,1180591620717411303424,9)).1) := by
  cbv; simp


-- Full seven-guard theorem application at ani_1_skip.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_skip c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_const.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_const c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_binop_imm.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_binop_imm c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_binop_reg.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_binop_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_binop_or.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_binop_or c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_shift_zero.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_shift_zero c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_shift_reg.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_shift_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_div.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_long_mul.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_long_mul c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_long_div.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_long_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_addCarry.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_addCarry c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_addOverflow.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_addOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_subOverflow.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_subOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_load.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_load c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_store.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_store c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_load16.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_load16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_store16.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_store16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_load32.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_load32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_store32.
example (c : AsmConfigExact 1) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 1)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_1_store32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_1_fpLess.


-- Full seven-guard theorem application at ani_1_fpLessEqual.


-- Full seven-guard theorem application at ani_1_fpEqual.


-- Full seven-guard theorem application at ani_1_fpAbs.


-- Full seven-guard theorem application at ani_1_fpNeg.


-- Full seven-guard theorem application at ani_1_fpSqrt.


-- Full seven-guard theorem application at ani_1_fpAdd.


-- Full seven-guard theorem application at ani_1_fpSub.


-- Full seven-guard theorem application at ani_1_fpMul.


-- Full seven-guard theorem application at ani_1_fpDiv.


-- Full seven-guard theorem application at ani_1_fpFma.


-- Full seven-guard theorem application at ani_1_fpMov.


-- Full seven-guard theorem application at ani_1_fpMovToReg.


-- Full seven-guard theorem application at ani_1_fpMovFromReg.


-- Full seven-guard theorem application at ani_1_fpToInt.


-- Full seven-guard theorem application at ani_1_fpFromInt.


-- Full seven-guard theorem application at ani_2_skip.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_skip c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_const.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_const c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_binop_imm.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_binop_imm c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_binop_reg.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_binop_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_binop_or.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_binop_or c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_shift_zero.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_shift_zero c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_shift_one.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_shift_one c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_shift_reg.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_shift_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_div.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_long_mul.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_long_mul c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_long_div.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_long_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_addCarry.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_addCarry c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_addOverflow.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_addOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_subOverflow.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_subOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_load.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_load c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_store.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_store c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_load16.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_load16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_store16.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_store16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_load32.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_load32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_store32.
example (c : AsmConfigExact 2) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 2)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_2_store32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_2_fpLess.


-- Full seven-guard theorem application at ani_2_fpLessEqual.


-- Full seven-guard theorem application at ani_2_fpEqual.


-- Full seven-guard theorem application at ani_2_fpAbs.


-- Full seven-guard theorem application at ani_2_fpNeg.


-- Full seven-guard theorem application at ani_2_fpSqrt.


-- Full seven-guard theorem application at ani_2_fpAdd.


-- Full seven-guard theorem application at ani_2_fpSub.


-- Full seven-guard theorem application at ani_2_fpMul.


-- Full seven-guard theorem application at ani_2_fpDiv.


-- Full seven-guard theorem application at ani_2_fpFma.


-- Full seven-guard theorem application at ani_2_fpMov.


-- Full seven-guard theorem application at ani_2_fpMovToReg.


-- Full seven-guard theorem application at ani_2_fpMovFromReg.


-- Full seven-guard theorem application at ani_2_fpToInt.


-- Full seven-guard theorem application at ani_2_fpFromInt.


-- Full seven-guard theorem application at ani_8_skip.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_skip c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_const.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_const c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_binop_imm.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_binop_imm c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_binop_reg.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_binop_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_binop_or.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_binop_or c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_shift_zero.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_shift_zero c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_shift_one.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_shift_one c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_shift_reg.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_shift_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_div.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_long_mul.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_long_mul c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_long_div.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_long_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_addCarry.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_addCarry c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_addOverflow.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_addOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_subOverflow.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_subOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_load.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_load c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_store.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_store c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_load8.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_load8 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_store8.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_store8 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_load16.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_load16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_store16.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_store16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_load32.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_load32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_store32.
example (c : AsmConfigExact 8) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 8)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_8_store32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_8_fpLess.


-- Full seven-guard theorem application at ani_8_fpLessEqual.


-- Full seven-guard theorem application at ani_8_fpEqual.


-- Full seven-guard theorem application at ani_8_fpAbs.


-- Full seven-guard theorem application at ani_8_fpNeg.


-- Full seven-guard theorem application at ani_8_fpSqrt.


-- Full seven-guard theorem application at ani_8_fpAdd.


-- Full seven-guard theorem application at ani_8_fpSub.


-- Full seven-guard theorem application at ani_8_fpMul.


-- Full seven-guard theorem application at ani_8_fpDiv.


-- Full seven-guard theorem application at ani_8_fpFma.


-- Full seven-guard theorem application at ani_8_fpMov.


-- Full seven-guard theorem application at ani_8_fpMovToReg.


-- Full seven-guard theorem application at ani_8_fpMovFromReg.


-- Full seven-guard theorem application at ani_8_fpToInt.


-- Full seven-guard theorem application at ani_8_fpFromInt.


-- Full seven-guard theorem application at ani_32_skip.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_skip c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_const.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_const c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_binop_imm.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_binop_imm c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_binop_reg.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_binop_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_binop_or.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_binop_or c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_shift_zero.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_shift_zero c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_shift_one.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_shift_one c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_shift_reg.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_shift_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_div.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_long_mul.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_long_mul c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_long_div.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_long_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_addCarry.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_addCarry c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_addOverflow.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_addOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_subOverflow.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_subOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_load.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_load c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_store.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_store c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_load8.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_load8 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_store8.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_store8 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_load16.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_load16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_store16.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_store16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_load32.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_load32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_store32.
example (c : AsmConfigExact 32) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 32)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_32_store32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_32_fpLess.


-- Full seven-guard theorem application at ani_32_fpLessEqual.


-- Full seven-guard theorem application at ani_32_fpEqual.


-- Full seven-guard theorem application at ani_32_fpAbs.


-- Full seven-guard theorem application at ani_32_fpNeg.


-- Full seven-guard theorem application at ani_32_fpSqrt.


-- Full seven-guard theorem application at ani_32_fpAdd.


-- Full seven-guard theorem application at ani_32_fpSub.


-- Full seven-guard theorem application at ani_32_fpMul.


-- Full seven-guard theorem application at ani_32_fpDiv.


-- Full seven-guard theorem application at ani_32_fpFma.


-- Full seven-guard theorem application at ani_32_fpMov.


-- Full seven-guard theorem application at ani_32_fpMovToReg.


-- Full seven-guard theorem application at ani_32_fpMovFromReg.


-- Full seven-guard theorem application at ani_32_fpToInt.


-- Full seven-guard theorem application at ani_32_fpFromInt.


-- Full seven-guard theorem application at ani_64_skip.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_skip c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_const.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_const c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_binop_imm.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_binop_imm c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_binop_reg.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 1180591620717411303424 (.reg 4))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_binop_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_binop_or.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 2 (.reg 2))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_binop_or c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_shift_zero.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 1180591620717411303424 (.imm 0))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_shift_zero c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_shift_one.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsr 1180591620717411303424 2 (.imm 1))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_shift_one c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_shift_reg.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 1180591620717411303424 (.reg 8))) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_shift_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_div.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_long_mul.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_long_mul c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_long_div.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_long_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_addCarry.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_addCarry c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_addOverflow.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_addOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_subOverflow.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_subOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_load.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_load c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_store.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_store c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_load8.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_load8 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_store8.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_store8 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_load16.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_load16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_store16.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_store16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_load32.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_load32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_store32.
example (c : AsmConfigExact 64) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 64)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_64_store32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_64_fpLess.


-- Full seven-guard theorem application at ani_64_fpLessEqual.


-- Full seven-guard theorem application at ani_64_fpEqual.


-- Full seven-guard theorem application at ani_64_fpAbs.


-- Full seven-guard theorem application at ani_64_fpNeg.


-- Full seven-guard theorem application at ani_64_fpSqrt.


-- Full seven-guard theorem application at ani_64_fpAdd.


-- Full seven-guard theorem application at ani_64_fpSub.


-- Full seven-guard theorem application at ani_64_fpMul.


-- Full seven-guard theorem application at ani_64_fpDiv.


-- Full seven-guard theorem application at ani_64_fpFma.


-- Full seven-guard theorem application at ani_64_fpMov.


-- Full seven-guard theorem application at ani_64_fpMovToReg.


-- Full seven-guard theorem application at ani_64_fpMovFromReg.


-- Full seven-guard theorem application at ani_64_fpToInt.


-- Full seven-guard theorem application at ani_64_fpFromInt.


-- Full seven-guard theorem application at ani_64_wide_ignored_second.


-- Full seven-guard theorem application at ani_80_skip.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.skip) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_skip c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_const.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.const 1180591620717411303424 7) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_const c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_binop_imm.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .add 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_binop_imm c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_binop_reg.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .xor 1180591620717411303424 2 (.reg 4))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_binop_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_binop_or.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.binop .or 1180591620717411303424 1180591620717411303424 (.reg 2))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_binop_or c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_shift_zero.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsl 1180591620717411303424 2 (.imm 0))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_shift_zero c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_shift_one.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .lsr 1180591620717411303424 1180591620717411303424 (.imm 1))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_shift_one c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_shift_reg.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.shift .asr 1180591620717411303424 2 (.reg 8))) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_shift_reg c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_div.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv8, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.div 1180591620717411303424 2 4)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_long_mul.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .armv7, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longMul 6 0 0 4)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_long_mul c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_long_div.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .x86_64, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.longDiv 0 6 6 0 1180591620717411303424)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_long_div c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_addCarry.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addCarry 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_addCarry c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_addOverflow.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.addOverflow 1180591620717411303424 1180591620717411303424 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_addOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_subOverflow.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.arith (.subOverflow 1180591620717411303424 2 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_subOverflow c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_load.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_load c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_store.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_store c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_load8.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_load8 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_store8.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store8 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_store8 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_load16.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_load16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_store16.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store16 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_store16 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_load32.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := true, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .load32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_load32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_store32.
example (c : AsmConfigExact 80) : stackAsmName ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) (compNative ({ c with isa := .riscv, regCount := 10, avoidRegs := [1180591620717411303424,1180591620717411303424], fpRegCount := 4, twoRegArith := false, validImm := fun _ v => v == 1, addrOffset := (0,100), hwOffset := (0,2), byteOffset := (0,3) }) false (.inst (.mem .store32 1180591620717411303424 (.addr 2 0)) : WordLangProgHOL (BitVec 80)) (.append (.list [8]) (.list [2]),99) (5,1180591620717411303424,9)).1 := by
  obtain ⟨plain, conventions, valid, twoReg, noShare, room, minimum⟩ := guard_ani_80_store32 c
  exact wordToStackStackAsmNameInst _ _ _ _ _ plain conventions valid twoReg noShare room minimum

-- Full seven-guard theorem application at ani_80_fpLess.


-- Full seven-guard theorem application at ani_80_fpLessEqual.


-- Full seven-guard theorem application at ani_80_fpEqual.


-- Full seven-guard theorem application at ani_80_fpAbs.


-- Full seven-guard theorem application at ani_80_fpNeg.


-- Full seven-guard theorem application at ani_80_fpSqrt.


-- Full seven-guard theorem application at ani_80_fpAdd.


-- Full seven-guard theorem application at ani_80_fpSub.


-- Full seven-guard theorem application at ani_80_fpMul.


-- Full seven-guard theorem application at ani_80_fpDiv.


-- Full seven-guard theorem application at ani_80_fpFma.


-- Full seven-guard theorem application at ani_80_fpMov.


-- Full seven-guard theorem application at ani_80_fpMovToReg.


-- Full seven-guard theorem application at ani_80_fpMovFromReg.


-- Full seven-guard theorem application at ani_80_fpToInt.


-- Full seven-guard theorem application at ani_80_fpFromInt.


end Flapjack.Test.WordToStackAsmNameInstructionsParity
