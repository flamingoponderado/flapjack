(* Fresh direct original native asmSem FP observations; no Lab evaluator. *)
load "preamble";
load "asmSemTheory";
load "machine_ieeeTheory";
load "binary_ieeeLib";
load "isqrtLib";
open bossLib HolKernel Parse preamble asmSemTheory asmTheory machine_ieeeTheory binary_ieeeTheory;
val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def,
  fp64_lessThan_def, fp64_lessEqual_def, fp64_equal_def, fp64_abs_def, fp64_negate_def,
  fp64_sqrt_def, fp64_add_def, fp64_sub_def, fp64_mul_def, fp64_div_def,
  fp64_mul_add_def, fp64_to_int_def, int_to_fp64_def, real_to_fp64_def,
  real_to_float_def];
fun print_eval label q = (print label; print "="; print_term (rconc (EVAL q)); print "\n");
val s64 = ``(s : 64 asmSem$asm_state)``;
val s32 = ``(s : 32 asmSem$asm_state)``;
val s8 = ``(s : 8 asmSem$asm_state)``;
val s128 = ``(s : 128 asmSem$asm_state)``;
val _ = print_eval "asm_fp_less_nan" ``(asmSem$fp_upd (FPLess 1 2 3) (^s64 with fp_regs := K 0x7ff8000000000001w)).regs 1 = 0w``;
val _ = print_eval "asm_fp_less_equal_zero" ``(asmSem$fp_upd (FPLessEqual 1 2 3) (^s64 with fp_regs := (\r. if r = 2 then 0x8000000000000000w else 0w))).regs 1 = 1w``;
val _ = print_eval "asm_fp_equal_nan" ``(asmSem$fp_upd (FPEqual 1 2 3) (^s64 with fp_regs := K 0x7ff8000000000001w)).regs 1 = 0w``;
val _ = print_eval "asm_fp_equal_zero" ``(asmSem$fp_upd (FPEqual 1 2 3) (^s64 with fp_regs := K 0w)).regs 1 = 1w``;
val _ = print_eval "asm_fp_mov_payload" ``(asmSem$fp_upd (FPMov 1 2) (^s64 with fp_regs := K 0x7ff8000000000001w)).fp_regs 1 = 0x7ff8000000000001w``;
val _ = print_eval "asm_fp_abs_payload" ``(asmSem$fp_upd (FPAbs 1 2) (^s64 with fp_regs := K 0xfff8000000000001w)).fp_regs 1 = 0x7ff8000000000001w``;
val _ = print_eval "asm_fp_neg_zero" ``(asmSem$fp_upd (FPNeg 1 2) (^s64 with fp_regs := K 0x8000000000000000w)).fp_regs 1 = 0w``;
val _ = print_eval "asm_fp_sqrt_four" ``(asmSem$fp_upd (FPSqrt 1 2) (^s64 with fp_regs := K 0x4010000000000000w)).fp_regs 1 = 0x4000000000000000w``;
val _ = print_eval "asm_fp_add_two" ``(asmSem$fp_upd (FPAdd 1 2 3) (^s64 with fp_regs := K 0x3ff0000000000000w)).fp_regs 1 = 0x4000000000000000w``;
val _ = print_eval "asm_fp_sub_zero" ``(asmSem$fp_upd (FPSub 1 2 3) (^s64 with fp_regs := K 0x3ff0000000000000w)).fp_regs 1 = 0w``;
val _ = print_eval "asm_fp_mul_four" ``(asmSem$fp_upd (FPMul 1 2 3) (^s64 with fp_regs := K 0x4000000000000000w)).fp_regs 1 = 0x4010000000000000w``;
val _ = print_eval "asm_fp_div_half" ``(asmSem$fp_upd (FPDiv 1 2 3) (^s64 with fp_regs := (\r. if r = 2 then 0x3ff0000000000000w else 0x4000000000000000w))).fp_regs 1 = 0x3fe0000000000000w``;
val _ = print_eval "asm_fp_fma_order" ``(asmSem$fp_upd (FPFma 1 2 3) (^s64 with fp_regs := (\r. if r = 1 then 0x3ff0000000000000w else if r = 2 then 0x4000000000000000w else 0x4008000000000000w))).fp_regs 1 = 0x401c000000000000w``;
val _ = print_eval "asm_fp_to_reg64" ``(asmSem$fp_upd (FPMovToReg 1 2 3) (^s64 with fp_regs := K 0x7ff8000000000001w)).regs 1 = 0x7ff8000000000001w``;
val _ = print_eval "asm_fp_to_reg_alias32" ``(asmSem$fp_upd (FPMovToReg 1 1 3) (^s32 with fp_regs := K 0x123456789abcdef0w)).regs 1 = 0x12345678w``;
val _ = print_eval "asm_fp_from_reg64" ``(asmSem$fp_upd (FPMovFromReg 1 2 3) (^s64 with regs := K (0x123456789abcdef0w))).fp_regs 1 = 0x123456789abcdef0w``;
val _ = print_eval "asm_fp_from_reg32" ``(asmSem$fp_upd (FPMovFromReg 1 2 3) (^s32 with regs := (\r. if r = 2 then 0x9abcdef0w else 0x12345678w))).fp_regs 1 = 0x123456789abcdef0w``;
val _ = print_eval "asm_fp_from_reg8" ``(asmSem$fp_upd (FPMovFromReg 1 2 3) (^s8 with regs := (\r. if r = 2 then 0x34w else 0x12w))).fp_regs 1 = 0x1234w``;
val _ = print_eval "asm_fp_to_int_tie_even" ``(asmSem$fp_upd (FPToInt 1 2) (^s64 with fp_regs := K 0x4004000000000000w)).fp_regs 1 = 2w``;
val _ = print_eval "asm_fp_to_int_negative" ``(asmSem$fp_upd (FPToInt 1 2) (^s64 with fp_regs := K 0xbff0000000000000w)).fp_regs 1 = 0xffffffffw``;
val _ = print_eval "asm_fp_to_int_overflow_bits" ``(asmSem$fp_upd (FPToInt 1 2) (^s64 with <|fp_regs := K 0x41e0000000000000w; failed := F|>)).fp_regs 1 = 0x80000000w``;
val _ = print_eval "asm_fp_to_int_overflow_failed" ``(asmSem$fp_upd (FPToInt 1 2) (^s64 with <|fp_regs := K 0x41e0000000000000w; failed := F|>)).failed``;
val _ = print_eval "asm_fp_to_int_inf_error" ``(asmSem$fp_upd (FPToInt 1 2) (^s64 with <|fp_regs := K 0x7ff0000000000000w; failed := F|>)).failed``;
val _ = print_eval "asm_fp_to_int_odd32" ``(asmSem$fp_upd (FPToInt 3 2) (^s32 with fp_regs := (\r. if r = 2 then 0x4000000000000000w else 0x123456789abcdef0w))).fp_regs 1 = 0x000000029abcdef0w``;
val _ = print_eval "asm_fp_from_int64" ``(asmSem$fp_upd (FPFromInt 1 2) (^s64 with fp_regs := K 0xffffffffw)).fp_regs 1 = 0xbff0000000000000w``;
val _ = print_eval "asm_fp_from_int32" ``(asmSem$fp_upd (FPFromInt 1 3) (^s32 with fp_regs := K 0xffffffff00000000w)).fp_regs 1 = 0xbff0000000000000w``;
val _ = print_eval "asm_fp_from_int8" ``(asmSem$fp_upd (FPFromInt 1 3) (^s8 with fp_regs := K 0xffffffff00000000w)).fp_regs 1 = 0xbff0000000000000w``;
val _ = print_eval "asm_fp_from_int128" ``(asmSem$fp_upd (FPFromInt 1 2) (^s128 with fp_regs := K 0xffffffffw)).fp_regs 1 = 0x41efffffffe00000w``;
val _ = print_eval "asm_fp_to_int_lower_alias32" ``(asmSem$fp_upd (FPToInt 4 2) (^s32 with fp_regs := K 0x4000000000000000w)).fp_regs 2 = 0x4000000000000002w``;
val _ = print_eval "asm_fp_to_int_upper_alias32" ``(asmSem$fp_upd (FPToInt 5 2) (^s32 with fp_regs := K 0x4000000000000000w)).fp_regs 2 = 0x0000000200000000w``;
val _ = print_eval "asm_fp_to_int_overflow32" ``let t = asmSem$fp_upd (FPToInt 3 2) (^s32 with <|fp_regs := (\r. if r=2 then 0x41e0000000000000w else 0x123456789abcdef0w); failed := F|>) in t.fp_regs 1 = 0x800000009abcdef0w /\ t.failed``;
val _ = print_eval "asm_fp_to_reg8" ``let t = asmSem$fp_upd (FPMovToReg 1 2 3) (^s8 with fp_regs := K 0x123456789abcdef0w) in t.regs 1 = 0xf0w /\ t.regs 2 = 0x78w``;
val _ = print_eval "asm_fp_from_reg128" ``(asmSem$fp_upd (FPMovFromReg 1 2 3) (^s128 with regs := (\r. if r=2 then 0x11112222333344445555666677778888w else 0x9999w))).fp_regs 1 = 0x5555666677778888w``;
val _ = print_eval "asm_fp_prior_failure" ``let t = asmSem$fp_upd (FPAdd 1 2 3) (^s64 with <|fp_regs := K 0x3ff0000000000000w; failed := T|>) in t.fp_regs 1 = 0x4000000000000000w /\ t.failed``;
