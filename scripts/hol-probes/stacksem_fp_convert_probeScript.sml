(*
  Original StackSem inst_def FP real-conversion observations from
  cakeml/compiler/backend/semantics/stackSemScript.sml: FPSqrt :559-562,
  FPToInt :605-624 and FPFromInt :625-640.  The 64-bit rows use a
  (64,unit,unit) state and the width-split rows a (32,unit,unit) state.  FPSqrt
  is probed on the exact square 4.0 (whose sqrt isqrtLib decides); FPToInt
  covers an in-range value, an out-of-range value that fails the `w2i (i2w i) =
  i` word32 round-trip, the 32-bit low/high `bit_field_insert` split, and a
  missing operand; FPFromInt covers the 64-bit low-32-bit read, the 32-bit
  low/high half selection and a missing operand.  binary_ieeeLib and the
  machine_ieee fp64 definitions extend EVAL with the conversions.
*)
load "bossLib";
load "preamble";
load "stackSemTheory";
load "machine_ieeeTheory";
load "binary_ieeeLib";
load "isqrtLib";
open bossLib HolKernel Parse preamble stackSemTheory machine_ieeeTheory binary_ieeeTheory;
val _ = computeLib.add_funs [fp64_to_float_def, float_to_fp64_def,
  fp64_sqrt_def, fp64_to_int_def, int_to_fp64_def, real_to_fp64_def,
  real_to_float_def];

fun observe label q = let val th = EVAL q in
  print (label ^ "="); print_term (rconc th); print "\n" end;

fun row label state inst = observe label (``case stackSem$inst ^inst ^state of
    NONE => NONE
  | SOME t => SOME (t.clock,
      OPTION_MAP w2n (FLOOKUP t.fp_regs 7),
      OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 4),
      OPTION_MAP (\x. case x of Word w => INL (w2n w) | Loc a b => INR (a,b)) (FLOOKUP t.regs 5))``);

fun st64 fp = ``(ARB : (64,unit,unit) stackSem$state) with <|
  clock := 6;
  regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2)
                |+ (4,Word 77w) |+ (5,Loc 4 5);
  fp_regs := ^fp |>``;
fun st32 fp = ``(ARB : (32,unit,unit) stackSem$state) with <|
  clock := 6;
  regs := FEMPTY |+ (1,Word 10w) |+ (2,Word 20w) |+ (3,Loc 1 2)
                |+ (4,Word 77w) |+ (5,Loc 4 5);
  fp_regs := ^fp |>``;

val one   = ``0x3FF0000000000000w : word64``;
val two   = ``0x4000000000000000w : word64``;
val three = ``0x4008000000000000w : word64``;
val six   = ``0x4018000000000000w : word64``;
val ten   = ``0x4024000000000000w : word64``;

val base64 = ``(FEMPTY : num |-> word64) |+ (1,^one) |+ (2,^two) |+ (3,^three) |+ (4,^six) |+ (7,^ten)``;
val sqrt64 = ``(FEMPTY : num |-> word64) |+ (1,^one) |+ (2,0x4010000000000000w) |+ (3,^three) |+ (4,^six) |+ (7,^ten)``;
val big64  = ``(FEMPTY : num |-> word64) |+ (1,^one) |+ (2,0x4330000000000000w) |+ (3,^three) |+ (4,^six) |+ (7,^ten)``;
val int64  = ``(FEMPTY : num |-> word64) |+ (1,^one) |+ (2,0x0000000000000003w) |+ (3,^three) |+ (4,^six) |+ (7,^ten)``;
val v32    = ``(FEMPTY : num |-> word64) |+ (7,0x0000000300000004w)``;

val iSqrt72  = ``(FP (FPSqrt 7 2)) : 64 asm$inst``;
val iSqrt79  = ``(FP (FPSqrt 7 9)) : 64 asm$inst``;
val iToInt72 = ``(FP (FPToInt 7 2)) : 64 asm$inst``;
val iToInt79 = ``(FP (FPToInt 7 9)) : 64 asm$inst``;
val iToInt14 = ``(FP (FPToInt 14 2)) : 32 asm$inst``;
val iToInt15 = ``(FP (FPToInt 15 2)) : 32 asm$inst``;
val iFrom72  = ``(FP (FPFromInt 7 2)) : 64 asm$inst``;
val iFrom79  = ``(FP (FPFromInt 7 9)) : 64 asm$inst``;
val iFrom714 = ``(FP (FPFromInt 7 14)) : 32 asm$inst``;
val iFrom715 = ``(FP (FPFromInt 7 15)) : 32 asm$inst``;

(* FPSqrt 7 2 with fp2 = 4.0 gives 2.0; missing fp9 fails. *)
val _ = row "fpsqrt_result" (st64 sqrt64) iSqrt72;
val _ = row "fpsqrt_missing" (st64 base64) iSqrt79;

(* FPToInt 7 2 with fp2 = 2.0 stores 2w; fp2 = 2^52 fails the word32
   round-trip; missing fp9 fails. *)
val _ = row "fptoint_result" (st64 base64) iToInt72;
val _ = row "fptoint_out_of_range" (st64 big64) iToInt72;
val _ = row "fptoint_missing" (st64 base64) iToInt79;

(* 32-bit FPToInt writes the low (d1=14) or high (d1=15) half of fp7 (register index d1 DIV 2). *)
val _ = row "fptoint32_even" (st32 base64) iToInt14;
val _ = row "fptoint32_odd" (st32 base64) iToInt15;

(* FPFromInt 7 2 reads the low 32 bits (3) into 3.0; missing fp9 fails. *)
val _ = row "fpfromint_result" (st64 int64) iFrom72;
val _ = row "fpfromint_missing" (st64 base64) iFrom79;

(* 32-bit FPFromInt reads the low (d2=14 -> 4) or high (d2=15 -> 3) half of
   fp7 = 0x0000000300000004. *)
val _ = row "fpfromint32_even" (st32 v32) iFrom714;
val _ = row "fpfromint32_odd" (st32 v32) iFrom715;
