(*
  Direct HOL-EVAL fixture for wordSem inst_def
  (cakeml/compiler/backend/semantics/wordSemScript.sml:716-939) ported in
  Flapjack/Compiler/Backend/Semantics/WordSem/Inst.lean, at 64-bit words:
  integer arithmetic, memory, and floating-point instructions (sqrt only on an
  exact square, via isqrtLib).  States are record updates of a free state s;
  rows observe projections.
*)
load "bossLib";
load "preamble";
load "wordSemTheory";
load "binary_ieeeLib";
load "isqrtLib";
open bossLib;
open HolKernel Parse;
open preamble;
open wordSemTheory machine_ieeeTheory binary_ieeeTheory fpSemTheory;

val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def, fp64_lessThan_def,
  fp64_lessEqual_def, fp64_equal_def, fp64_abs_def, fp64_negate_def, fp64_sqrt_def,
  fp64_add_def, fp64_sub_def, fp64_mul_def, fp64_div_def, fp64_mul_add_def,
  fp64_to_int_def, int_to_fp64_def, real_to_fp64_def, real_to_float_def];

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rhs (concl th));
    print "\n"
  end;

val s = ``s:(64,'c,'ffi) wordSem$state``;
val st = ``^s with <|
  locals := fromAList [(2, Word 17w); (3, Word 5w); (4, Word 0w);
                       (10, Word 0xFFFFFFFFFFFFFFFFw); (11, Word 1w);
                       (12, Word 0x7FFFFFFFFFFFFFFFw); (13, Word 0x8000000000000000w);
                       (14, Word 0x8000000000000000w); (15, Word 4w);
                       (20, Word 1w); (21, Word 0w); (22, Word 3w); (23, Word 5w);
                       (30, Word 16w); (31, Word 0xABw); (32, Loc 1 2)];
  memory := (\a. if a = 16w then Word 0x1122334455667788w else Loc 0 0);
  mdomain := {16w}; be := F;
  fp_regs := FEMPTY |+ (1, 0x3FF0000000000000w) |+ (2, 0x4000000000000000w)
                    |+ (4, 0x4010000000000000w) |+ (5, 0x4004000000000000w)
                    |+ (6, 0x4415AF1D78B58C40w) |>``;
fun pl label inst ks =
  print_eval label ``OPTION_MAP (\t:(64,'c,'ffi) wordSem$state. MAP (\k. lookup k t.locals) ^ks)
    (inst ^inst ^st)``;
fun pf label inst ks =
  print_eval label ``OPTION_MAP (\t:(64,'c,'ffi) wordSem$state. MAP (\k. FLOOKUP t.fp_regs k) ^ks)
    (inst ^inst ^st)``;
fun pn label inst = print_eval label ``inst ^inst ^st = NONE``;

val _ = pl "div" ``Arith (Div 1 2 3) : 64 inst`` ``[1] : num list``;
val _ = pn "div_zero" ``Arith (Div 1 2 4) : 64 inst``;
val _ = pl "add_carry" ``Arith (AddCarry 1 10 11 4) : 64 inst`` ``[1;4] : num list``;
val _ = pl "add_overflow" ``Arith (AddOverflow 1 12 11 4) : 64 inst`` ``[1;4] : num list``;
val _ = pl "sub_overflow" ``Arith (SubOverflow 1 13 11 4) : 64 inst`` ``[1;4] : num list``;
val _ = pl "long_mul" ``Arith (LongMul 1 2 14 15) : 64 inst`` ``[1;2] : num list``;
val _ = pl "long_div" ``Arith (LongDiv 1 2 20 21 22) : 64 inst`` ``[1;2] : num list``;
val _ = pn "long_div_big" ``Arith (LongDiv 1 2 23 21 22) : 64 inst``;
val _ = pl "binop_imm" ``Arith (Binop Add 1 2 (Imm 5w)) : 64 inst`` ``[1] : num list``;
val _ = pl "shift_reg" ``Arith (Shift Lsr 1 2 (Reg 3)) : 64 inst`` ``[1] : num list``;
val _ = pl "const" ``Const 7 99w : 64 inst`` ``[7] : num list``;
val _ = pl "load" ``Mem Load 1 (Addr 30 0w) : 64 inst`` ``[1] : num list``;
val _ = pl "load8" ``Mem Load8 1 (Addr 30 1w) : 64 inst`` ``[1] : num list``;
val _ = pl "load32" ``Mem Load32 1 (Addr 30 4w) : 64 inst`` ``[1] : num list``;
val _ = pn "load_miss" ``Mem Load 1 (Addr 30 8w) : 64 inst``;
val _ = pn "load16" ``Mem Load16 1 (Addr 30 0w) : 64 inst``;
val _ = print_eval "store8"
  ``OPTION_MAP (\t:(64,'c,'ffi) wordSem$state. t.memory 16w) (inst (Mem Store8 31 (Addr 30 2w)) ^st)``;
val _ = print_eval "store"
  ``OPTION_MAP (\t:(64,'c,'ffi) wordSem$state. t.memory 16w) (inst (Mem Store 32 (Addr 30 0w)) ^st)``;
val _ = pn "store16" ``Mem Store16 31 (Addr 30 0w) : 64 inst``;
val _ = pl "fp_less" ``FP (FPLess 7 1 2) : 64 inst`` ``[7] : num list``;
val _ = pl "fp_equal" ``FP (FPEqual 7 1 2) : 64 inst`` ``[7] : num list``;
val _ = pf "fp_add" ``FP (FPAdd 3 1 2) : 64 inst`` ``[3] : num list``;
val _ = pf "fp_div" ``FP (FPDiv 3 1 2) : 64 inst`` ``[3] : num list``;
val _ = pf "fp_sqrt" ``FP (FPSqrt 3 4) : 64 inst`` ``[3] : num list``;
val _ = pf "fp_fma" ``FP (FPFma 1 2 4) : 64 inst`` ``[1] : num list``;
val _ = pf "fp_neg" ``FP (FPNeg 3 2) : 64 inst`` ``[3] : num list``;
val _ = pl "fp_mov_to_reg" ``FP (FPMovToReg 7 8 1) : 64 inst`` ``[7] : num list``;
val _ = pf "fp_mov_from_reg" ``FP (FPMovFromReg 3 2 0) : 64 inst`` ``[3] : num list``;
val _ = pf "fp_to_int" ``FP (FPToInt 3 5) : 64 inst`` ``[3] : num list``;
val _ = pn "fp_to_int_big" ``FP (FPToInt 3 6) : 64 inst``;
val _ = pf "fp_from_int" ``FP (FPFromInt 3 2) : 64 inst`` ``[3] : num list``;
val _ = pn "fp_missing" ``FP (FPAdd 3 1 9) : 64 inst``;
