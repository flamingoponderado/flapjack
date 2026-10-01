load "preamble";
load "wordLangTheory";
open bossLib HolKernel Parse preamble wordLangTheory;
fun out label q = (print (label ^ "="); print_term (rconc (EVAL q)); print "\n");
val _ = out "mi_skip" ``let i = (Skip:64 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val _ = out "mi_const" ``let i = (Const 1208925819614629174706176 3w:64 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val _ = out "mi_binreg" ``let i = (Arith (Binop Add 2 9 (Reg 7)):64 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val _ = out "mi_binimm" ``let i = (Arith (Binop Add 2 9 (Imm 999w)):64 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val _ = out "mi_shift" ``let i = (Arith (Shift Lsl 11 9 (Reg 17)):64 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val _ = out "mi_div" ``let i = (Arith (Div 9 21 7):64 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val _ = out "mi_longdiv" ``let i = (Arith (LongDiv 1 2 3 4 99):64 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val _ = out "mi_load8" ``let i = (Mem Load8 2 (Addr 80 7w):64 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val _ = out "mi_fp64_to" ``let i = (FP (FPMovToReg 2 99 100):64 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val _ = out "mi_fp32_to" ``let i = (FP (FPMovToReg 2 99 100):32 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val _ = out "mi_fp80_from" ``let i = (FP (FPMovFromReg 100 2 99):80 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val _ = out "mi_fpignored" ``let i = (FP (FPAdd 100 200 300):64 asm$inst) in (max_var_inst i, every_var_inst (\r. r <= max_var_inst i) i)``;
val th = Q.prove (`!inst. every_var_inst (\x. x <= max_var_inst inst) inst`,
  ho_match_mp_tac max_var_inst_ind THEN
  srw_tac[][every_var_inst_def,max_var_inst_def] THEN
  gvs [oneline every_var_imm_def, AllCaseEqs()] THEN
  TOP_CASE_TAC THEN simp []);
val _ = (print "mi_original_theorem="; print_thm th; print "\n");
