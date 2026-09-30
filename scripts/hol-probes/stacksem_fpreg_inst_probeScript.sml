(* Original StackSem inst_def register/sign observations, including aliases. *)
load "bossLib";
load "preamble";
load "stackSemTheory";
load "machine_ieeeTheory";
load "binary_ieeeLib";
open bossLib HolKernel Parse preamble stackSemTheory machine_ieeeTheory;
val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def, fp64_abs_def, fp64_negate_def];
fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;
val _ = observe "fpreg_mov_nan" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMov 7 1)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_mov_missing" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMov 7 9)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_abs_nan" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPAbs 7 1)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_abs_zero" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPAbs 7 3)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_neg_nan" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPNeg 7 1)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_neg_zero" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPNeg 7 4)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_abs_missing" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPAbs 7 9)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_neg_missing" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPNeg 7 9)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_to64" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovToReg 4 5 2)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_to32" ``let s = ((ARB : (32,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovToReg 4 5 2)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_to8" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovToReg 4 5 2)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_to32_alias" ``let s = ((ARB : (32,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovToReg 4 4 2)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_to_missing" ``let s = ((ARB : (32,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovToReg 4 5 9)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_from64_ignore" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovFromReg 7 1 9)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_from64_loc" ``let s = ((ARB : (64,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovFromReg 7 3 1)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_from32" ``let s = ((ARB : (32,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovFromReg 7 1 2)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_from8" ``let s = ((ARB : (8,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovFromReg 7 1 2)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_from32_missing" ``let s = ((ARB : (32,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovFromReg 7 1 9)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_from32_loc" ``let s = ((ARB : (32,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovFromReg 7 1 3)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
val _ = observe "fpreg_from32_alias" ``let s = ((ARB : (32,unit,unit) stackSem$state) with <|
 clock := 6; regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2) |+ (4,Word 77w) |+ (5,Loc 4 5);
 fp_regs := FEMPTY |+ (1,0xfff0000000000001w) |+ (2,0x1122334455667788w) |+ (3,0x8000000000000000w) |+ (4,0w)|>) in
 case inst (FP (FPMovFromReg 7 1 1)) s of NONE => NONE | SOME t => SOME (t.clock,
 OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
 OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``;
