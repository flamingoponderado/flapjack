(*
  Original StackSem inst_def FP comparison/arithmetic observations from
  cakeml/compiler/backend/semantics/stackSemScript.sml:519-542 (FPLess,
  FPLessEqual, FPEqual) and :563-587 (FPAdd, FPSub, FPMul, FPDiv, FPFma).
  The FPFma clause calls fpSem$fpfma (fpSemScript.sml:60-62), whose first
  argument is the addend permuted to the last fp64_mul_add slot.  binary_ieeeLib
  and the machine_ieee fp64 definitions extend EVAL with the arithmetic.
*)
load "bossLib";
load "preamble";
load "stackSemTheory";
load "machine_ieeeTheory";
load "binary_ieeeLib";
load "fpSemTheory";
open bossLib HolKernel Parse preamble stackSemTheory machine_ieeeTheory fpSemTheory;
val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def,
  fp64_lessThan_def, fp64_lessEqual_def, fp64_equal_def,
  fp64_add_def, fp64_sub_def, fp64_mul_def, fp64_div_def,
  fp64_mul_add_def, fpfma_def];

fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;

val one   = ``0x3FF0000000000000w : word64``;
val two   = ``0x4000000000000000w : word64``;
val three = ``0x4008000000000000w : word64``;
val six   = ``0x4018000000000000w : word64``;
val ten   = ``0x4024000000000000w : word64``;

val _ = observe "fpless_true" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPLess 4 1 2)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fpless_false" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPLess 4 2 1)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fpless_equal" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPLess 4 1 1)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fpless_missing" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPLess 4 1 9)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fplessequal_true" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPLessEqual 4 1 1)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fplessequal_false" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPLessEqual 4 2 1)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fpequal_true" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPEqual 4 1 1)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fpequal_false" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPEqual 4 1 2)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fpadd_result" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPAdd 7 1 2)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fpadd_missing" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPAdd 7 1 9)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fpsub_result" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPSub 7 3 1)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fpmul_result" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPMul 7 2 3)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fpdiv_result" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPDiv 7 4 2)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;

val _ = observe "fpfma_order" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)|>) in
 case inst (FP (FPFma 7 2 3)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
