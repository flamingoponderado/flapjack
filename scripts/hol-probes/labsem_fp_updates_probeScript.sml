load "preamble";
load "labSemTheory";
load "machine_ieeeTheory";
load "binary_ieeeLib";
load "isqrtLib";
load "fpSemTheory";
open bossLib HolKernel Parse preamble labSemTheory asmTheory machine_ieeeTheory binary_ieeeTheory fpSemTheory;
val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def,
  fp64_lessThan_def, fp64_lessEqual_def, fp64_equal_def, fp64_abs_def, fp64_negate_def,
  fp64_sqrt_def, fp64_add_def, fp64_sub_def, fp64_mul_def, fp64_div_def,
  fp64_mul_add_def, fpfma_def, fp64_to_int_def, int_to_fp64_def, real_to_fp64_def,
  real_to_float_def];
fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");
val s64 = ``(s : (64,unit,unit) labSem$state)``;
val s32 = ``(s : (32,unit,unit) labSem$state)``;
val s8 = ``(s : (8,unit,unit) labSem$state)``;
val s128 = ``(s : (128,unit,unit) labSem$state)``;
val _ = print_eval "lab_fp_less_nan" ``(fp_upd (FPLess 1 2 3) (^s64 with fp_regs := K 0x7ff8000000000001w)).regs 1 = Word 0w``;
val _ = print_eval "lab_fp_less_equal_zero" ``(fp_upd (FPLessEqual 1 2 3) (^s64 with fp_regs := (\r. if r = 2 then 0x8000000000000000w else 0w))).regs 1 = Word 1w``;
val _ = print_eval "lab_fp_equal_nan" ``(fp_upd (FPEqual 1 2 3) (^s64 with fp_regs := K 0x7ff8000000000001w)).regs 1 = Word 0w``;
val _ = print_eval "lab_fp_equal_zero" ``(fp_upd (FPEqual 1 2 3) (^s64 with fp_regs := K 0w)).regs 1 = Word 1w``;
val _ = print_eval "lab_fp_mov_payload" ``(fp_upd (FPMov 1 2) (^s64 with fp_regs := K 0x7ff8000000000001w)).fp_regs 1 = 0x7ff8000000000001w``;
val _ = print_eval "lab_fp_abs_payload" ``(fp_upd (FPAbs 1 2) (^s64 with fp_regs := K 0xfff8000000000001w)).fp_regs 1 = 0x7ff8000000000001w``;
val _ = print_eval "lab_fp_neg_zero" ``(fp_upd (FPNeg 1 2) (^s64 with fp_regs := K 0x8000000000000000w)).fp_regs 1 = 0w``;
val _ = print_eval "lab_fp_sqrt_four" ``(fp_upd (FPSqrt 1 2) (^s64 with fp_regs := K 0x4010000000000000w)).fp_regs 1 = 0x4000000000000000w``;
val _ = print_eval "lab_fp_add_two" ``(fp_upd (FPAdd 1 2 3) (^s64 with fp_regs := K 0x3ff0000000000000w)).fp_regs 1 = 0x4000000000000000w``;
val _ = print_eval "lab_fp_sub_zero" ``(fp_upd (FPSub 1 2 3) (^s64 with fp_regs := K 0x3ff0000000000000w)).fp_regs 1 = 0w``;
val _ = print_eval "lab_fp_mul_four" ``(fp_upd (FPMul 1 2 3) (^s64 with fp_regs := K 0x4000000000000000w)).fp_regs 1 = 0x4010000000000000w``;
val _ = print_eval "lab_fp_div_half" ``(fp_upd (FPDiv 1 2 3) (^s64 with fp_regs := (\r. if r = 2 then 0x3ff0000000000000w else 0x4000000000000000w))).fp_regs 1 = 0x3fe0000000000000w``;
val _ = print_eval "lab_fp_fma_order" ``(fp_upd (FPFma 1 2 3) (^s64 with fp_regs := (\r. if r = 1 then 0x3ff0000000000000w else if r = 2 then 0x4000000000000000w else 0x4008000000000000w))).fp_regs 1 = 0x401c000000000000w``;
val _ = print_eval "lab_fp_to_reg64" ``(fp_upd (FPMovToReg 1 2 3) (^s64 with fp_regs := K 0x7ff8000000000001w)).regs 1 = Word 0x7ff8000000000001w``;
val _ = print_eval "lab_fp_to_reg_alias32" ``(fp_upd (FPMovToReg 1 1 3) (^s32 with fp_regs := K 0x123456789abcdef0w)).regs 1 = Word 0x12345678w``;
val _ = print_eval "lab_fp_from_reg64" ``(fp_upd (FPMovFromReg 1 2 3) (^s64 with regs := K (Word 0x123456789abcdef0w))).fp_regs 1 = 0x123456789abcdef0w``;
val _ = print_eval "lab_fp_from_reg_loc_error" ``(fp_upd (FPMovFromReg 1 2 3) (^s64 with <|regs := K (Loc 4 5); failed := F|>)).failed``;
val _ = print_eval "lab_fp_from_reg32" ``(fp_upd (FPMovFromReg 1 2 3) (^s32 with regs := (\r. if r = 2 then Word 0x9abcdef0w else Word 0x12345678w))).fp_regs 1 = 0x123456789abcdef0w``;
val _ = print_eval "lab_fp_from_reg8" ``(fp_upd (FPMovFromReg 1 2 3) (^s8 with regs := (\r. if r = 2 then Word 0x34w else Word 0x12w))).fp_regs 1 = 0x1234w``;
val _ = print_eval "lab_fp_to_int_tie_even" ``(fp_upd (FPToInt 1 2) (^s64 with fp_regs := K 0x4004000000000000w)).fp_regs 1 = 2w``;
val _ = print_eval "lab_fp_to_int_negative" ``(fp_upd (FPToInt 1 2) (^s64 with fp_regs := K 0xbff0000000000000w)).fp_regs 1 = 0xffffffffw``;
val _ = print_eval "lab_fp_to_int_overflow_bits" ``(fp_upd (FPToInt 1 2) (^s64 with <|fp_regs := K 0x41e0000000000000w; failed := F|>)).fp_regs 1 = 0x80000000w``;
val _ = print_eval "lab_fp_to_int_overflow_failed" ``(fp_upd (FPToInt 1 2) (^s64 with <|fp_regs := K 0x41e0000000000000w; failed := F|>)).failed``;
val _ = print_eval "lab_fp_to_int_inf_error" ``(fp_upd (FPToInt 1 2) (^s64 with <|fp_regs := K 0x7ff0000000000000w; failed := F|>)).failed``;
val _ = print_eval "lab_fp_to_int_odd32" ``(fp_upd (FPToInt 3 2) (^s32 with fp_regs := (\r. if r = 2 then 0x4000000000000000w else 0x123456789abcdef0w))).fp_regs 1 = 0x000000029abcdef0w``;
val _ = print_eval "lab_fp_from_int64" ``(fp_upd (FPFromInt 1 2) (^s64 with fp_regs := K 0xffffffffw)).fp_regs 1 = 0xbff0000000000000w``;
val _ = print_eval "lab_fp_from_int32" ``(fp_upd (FPFromInt 1 3) (^s32 with fp_regs := K 0xffffffff00000000w)).fp_regs 1 = 0xbff0000000000000w``;
val _ = print_eval "lab_fp_from_int8" ``(fp_upd (FPFromInt 1 3) (^s8 with fp_regs := K 0xffffffff00000000w)).fp_regs 1 = 0xbff0000000000000w``;
val _ = print_eval "lab_fp_from_int128" ``(fp_upd (FPFromInt 1 2) (^s128 with fp_regs := K 0xffffffffw)).fp_regs 1 = 0x41efffffffe00000w``;
